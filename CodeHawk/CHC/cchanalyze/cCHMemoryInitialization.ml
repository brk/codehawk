(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma
   Copyright (c) 2024-2026 Aarno Labs LLC

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in all
   copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
   SOFTWARE.
   ============================================================================= *)

(* Byte-copy initialization proofs. Values and pointer validity are deliberately
   left to their own domains/checkers. Do not treat an opaque block write or an
   initializes-range effect as evidence about the copied source bytes. *)
open CHNumerical
open XprTypes
open CCHBasicTypes
open CCHLibTypes
open CCHBasicUtil
open CCHTypesCompare
open CCHTypesUtil
open CCHPreTypes
open CCHProofObligation
open CCHProofScaffolding
open CCHAnalysisTypes

let fenv = CCHFileEnvironment.file_environment

let constant = function XConst (IntConst n) -> Some n | _ -> None

let sizeof poq typ = constant (size_of_type poq#fenv typ)

let rec literal_value poq = function
  | Const (CInt (n, _, _)) -> Some (XConst (IntConst (mkNumericalFromInt64 n)))
  | SizeOf typ -> Some (size_of_type poq#fenv typ)
  | SizeOfE e ->
     (match type_of_exp poq#fenv e with
      | Ok typ -> Some (size_of_type poq#fenv typ)
      | _ -> None)
  | BinOp (Mult, left, right, typ) ->
     (match literal_value poq left, literal_value poq right with
      | Some (XConst (IntConst a)), Some (XConst (IntConst b)) ->
         let n = a#mult b in
         let range = range_of_type poq#fenv typ in
         if n#geq range#min && n#leq range#max then
           Some (XConst (IntConst n)) else None
      | _ -> None)
  | CastE (typ, e) ->
     (match fenv#get_type_unrolled typ, literal_value poq e with
      | TInt (ik, _), Some (XConst (IntConst n)) when ik <> IBool ->
         let range = range_of_type poq#fenv typ in
         if n#geq range#min && n#leq range#max then
           Some (XConst (IntConst n)) else None
      | _ -> None)
  | _ -> None

let rec addressed_local = function
  | CastE (typ, e)
       when (match fenv#get_type_unrolled typ with TPtr _ -> true | _ -> false) ->
     addressed_local e
  | AddrOf ((Var (_, vid), _) as lv)
  | StartOf ((Var (_, vid), _) as lv) when vid > 0 -> Some lv
  | _ -> None

(* Retain constant source pointer increments in bytes. The scale comes from
   the pointer expression before removing its casts, not from the root object.
   Unknown or negative increments are left to other proof paths. *)
let rec addressed_source poq = function
  | CastE (typ, e)
       when (match fenv#get_type_unrolled typ with TPtr _ -> true | _ -> false) ->
     addressed_source poq e
  | BinOp (PlusPI, e, index, _) ->
     (match addressed_source poq e, literal_value poq index,
            type_of_exp poq#fenv e with
      | Some (lv, start), Some x, Ok typ ->
         (match constant x, fenv#get_type_unrolled typ with
          | Some i, TPtr (elem, _) when i#geq numerical_zero ->
             (match sizeof poq elem with
              | Some sz when sz#gt numerical_zero ->
                 Some (lv, start#add (i#mult sz))
              | _ -> None)
          | _ -> None)
      | _ -> None)
  | e -> Option.map (fun lv -> lv, numerical_zero) (addressed_local e)

let local_type poq lv =
  match type_of_lval poq#fenv lv with
  | Ok typ -> Some (fenv#get_type_unrolled typ)
  | _ -> None

(* Remove a syntactic base offset without guessing structure layout. *)
let rec offset_suffix base off =
  match base, off with
  | NoOffset, _ -> Some off
  | Field (f, b), Field (g, o) when f = g -> offset_suffix b o
  | Index (i, b), Index (j, o) when exp_compare i j = 0 -> offset_suffix b o
  | _ -> None

(* Union members have offset zero. Ordinary structure layout, bitfields and
   nonconstant indices remain unsupported here rather than assuming an offset. *)
let rec relative_bytes poq typ off =
  match off with
  | NoOffset -> Some numerical_zero
  | Field ((name, _), rest) ->
     (match fenv#get_type_unrolled typ with
      | TComp (key, _) ->
         let comp = fenv#get_comp key in
         if comp.cstruct then None else
           (match List.find_opt (fun f -> f.fname = name) comp.cfields with
            | Some f when f.fbitfield = None -> relative_bytes poq f.ftype rest
            | _ -> None)
      | _ -> None)
  | Index (e, rest) ->
     (match fenv#get_type_unrolled typ, literal_value poq e with
      | TArray (elem, _, _), Some x ->
         (match constant x, sizeof poq elem, relative_bytes poq elem rest with
          | Some i, Some sz, Some tail when i#geq numerical_zero ->
             Some ((i#mult sz)#add tail)
          | _ -> None)
      | _ -> None)

(* One exact memset interval per local object. These are separate from value
   initialization markers: a write to any subobject invalidates the interval.
   Do not seed facts in functions whose lowered AST does not retain enough
   block-lifetime/control-flow information (loops/gotos/VLAs/assembly). *)
let local_range_enabled : (string, bool) Hashtbl.t = Hashtbl.create 17
let local_alias_enabled : (string, bool) Hashtbl.t = Hashtbl.create 17
let local_function_bodies : (string, fundec) Hashtbl.t = Hashtbl.create 17
let guarded_outputs_enabled : (string, bool) Hashtbl.t = Hashtbl.create 17
let guarded_output_contexts : (string, (int, bool) Hashtbl.t) Hashtbl.t =
  Hashtbl.create 17

(* A guarded output region is a value captured at one acyclic call site.
   It is not a malloc return, nor a claim of fresh/disjoint physical storage.
   Only an actual function-scope void* output slot and literal positive byte
   capacity are supported. Casts do not change the actual slot's C type. *)
let guarded_buffer_output (env: c_environment_int) (call: direct_callsite_int) =
  let fname = call#get_callee.vname in
  if Hashtbl.find_opt local_alias_enabled env#get_functionname <> Some true
     || not (CCHFileContract.file_contract#has_function_contract fname) then None else
  let predicates = List.filter (function XBufferOnReturn _ -> true | _ -> false)
      (CCHFileContract.file_contract#get_function_contract fname)#get_postconditions in
  let args = call#get_arguments in
  let argument n = if n > 0 && n <= List.length args then Some (List.nth args (n-1)) else None in
  let rec slot = function
    | CastE (typ, e) when is_pointer_type (fenv#get_type_unrolled typ) -> slot e
    | AddrOf (Var (_, vid), NoOffset) ->
       (match List.find_opt (fun vi -> vi.vid = vid && not vi.vglob && vi.vattr = [])
                  env#get_fdecls#get_locals with
        | Some vi -> (match fenv#get_type_unrolled vi.vtype with
            | TPtr (TVoid _, []) -> Some (vi, NoOffset)
            | _ -> None)
        | _ -> None)
    | _ -> None in
  let query = object method fenv = env#get_fdecls end in
  match predicates with
  | [XBufferOnReturn (_, _, ArgAddressedValue
       (ArgValue (ParFormal n, ArgNoOffset), ArgNoOffset), size) as predicate] ->
     let capacity = match size with
       | NumConstant n -> Some (XConst (IntConst n))
       | ArgValue (ParFormal m, ArgNoOffset) -> Option.bind (argument m) (literal_value query)
       | _ -> None in
     (match Option.bind (argument n) slot, capacity with
      | Some (vi, off), Some (XConst (IntConst capacity)) when capacity#gt numerical_zero ->
         let origin = env#mk_function_sideeffect_value call#get_location call#get_context
             call#get_callee (List.map (fun _ -> None) args) n vi.vtype in
         Some (vi, off, origin, capacity, predicate)
      | _ -> None)
  | _ -> None

let guarded_buffer_origin (env: c_environment_int) v =
  List.find_map (fun call -> match guarded_buffer_output env call with
      | Some (_, _, origin, capacity, predicate) when origin#equal v ->
         Some (call, capacity, predicate)
      | _ -> None) (proof_scaffolding#get_direct_callsites env#get_functionname)

let allocation_context (env: c_environment_int) v =
  if env#is_function_return_value v then env#get_callvar_context v else
    match guarded_buffer_origin env v with
    | Some (call, _, _) -> call#get_context
    | _ -> failwith "Unsupported allocation origin"

let capture_guarded_buffer_output (env: c_environment_int) ctxt =
  if not (proof_scaffolding#has_direct_callsite env#get_functionname ctxt) then [] else
    match guarded_buffer_output env (proof_scaffolding#get_direct_callsite env#get_functionname ctxt) with
    | Some (vi, off, origin, _, _) ->
       [CCHCommand.make_c_cmd (CHLanguage.ASSIGN_NUM
           (env#mk_program_var vi off CHLanguage.NUM_VAR_TYPE, CHLanguage.NUM_VAR origin))]
    | _ -> []

let local_byte_range_variable (env: c_environment_int) vi =
  env#mk_augmentation_variable "$initialized-bytes$" "local-byte-range"
    vi.vid CHLanguage.SYM_VAR_TYPE

let allocated_byte_range_variable (env: c_environment_int) ctxt =
  env#mk_augmentation_variable "$initialized-bytes$" "allocated-byte-range"
    (CCHContext.ccontexts#index_context ctxt) CHLanguage.SYM_VAR_TYPE

let allocated_byte_range_variables (env: c_environment_int) =
  List.filter_map (fun call ->
      if (call#get_header = "lib:stdlib" && call#get_callee.vname = "malloc")
         || Option.is_some (guarded_buffer_output env call) then
        Some (allocated_byte_range_variable env call#get_context)
      else None) (proof_scaffolding#get_direct_callsites env#get_functionname)

let allocated_live_variable (env: c_environment_int) ctxt =
  env#mk_augmentation_variable "$allocation-live$" "allocated-live"
    (CCHContext.ccontexts#index_context ctxt) CHLanguage.SYM_VAR_TYPE

let allocated_live_variables (env: c_environment_int) =
  List.filter_map (fun call ->
      if (call#get_header = "lib:stdlib" && call#get_callee.vname = "malloc")
         || Option.is_some (guarded_buffer_output env call) then
        Some (allocated_live_variable env call#get_context)
      else None) (proof_scaffolding#get_direct_callsites env#get_functionname)

let start_allocated_lifetime env ctxt =
  [CCHCommand.make_c_cmd (CHLanguage.ASSIGN_SYM
       (allocated_live_variable env ctxt,
        CHLanguage.SYM (new CHLanguage.symbol_t "allocated-live")))]

let local_byte_range_variables (env: c_environment_int) =
  List.map (local_byte_range_variable env) env#get_fdecls#get_locals
  @ allocated_byte_range_variables env

(* A local descriptor address may occur only as the complete argument of a
   modeled read-only field getter. This syntactic escape check is shared with
   guard transport: ordinary field assignments do not make an unescaped
   descriptor into an aliased return-status slot. *)
let readonly_descriptor_address_uses body vid =
  let contracts = CCHFileContract.file_contract in
  let getter_argument name index =
       if not (contracts#has_function_contract name) then false else
         let contract = contracts#get_function_contract name in
         contract#get_sideeffects = [XPreservesAllMemory]
         && List.exists (function
             | XRelationalExpr (Eq, ReturnValue,
                 ArgAddressedValue (ArgValue (ParFormal n, ArgNoOffset), ArgFieldOffset _))
               | XRelationalExpr (Eq,
                   ArgAddressedValue (ArgValue (ParFormal n, ArgNoOffset), ArgFieldOffset _), ReturnValue) ->
                n = index
             | _ -> false) contract#get_postconditions in
  let rec expression allowed = function
       | AddrOf ((Var (_, id), _) as lv) | StartOf ((Var (_, id), _) as lv) ->
          if id = vid then allowed && snd lv = NoOffset else lvalue lv
       | Lval lv -> lvalue lv
       | CastE (typ, e) when is_pointer_type (fenv#get_type_unrolled typ) -> expression allowed e
       | CastE (_, e) | UnOp (_, e, _) -> expression false e
       | BinOp (_, a, b, _) -> expression false a && expression false b
       | Const _ | SizeOf _ | AlignOf _ -> true
       | SizeOfE e | AlignOfE e -> expression false e
       | _ -> false
     and lvalue (host, off) =
       (match host with Var _ -> true | Mem e -> expression false e) && offset off
     and offset = function
       | NoOffset -> true | Field (_, o) -> offset o
       | Index (e, o) -> expression false e && offset o in
  let rec block b = List.for_all (fun s -> match s.skind with
         | Instr ins -> List.for_all (function
             | Set (lv, e, _) -> lvalue lv && expression false e
             | Call (lhs, fn, args, _) ->
                (match lhs with None -> true | Some lv -> lvalue lv)
                && expression false fn
                && List.for_all (fun (i, arg) ->
                    let allowed = match fn with
                      | Lval (Var (name, _), NoOffset) -> getter_argument name (i + 1)
                      | _ -> false in
                    expression allowed arg) (List.mapi (fun i x -> i, x) args)
             | _ -> false) ins
         | Return (e, _) -> (match e with None -> true | Some e -> expression false e)
         | If (e, a, b, _) -> expression false e && block a && block b
         | Block b -> block b | _ -> false) b.bstmts in
  block body.sbody

let register_local_byte_ranges (env: c_environment_int) (f: fundec) =
  Hashtbl.replace local_function_bodies env#get_functionname f;
  let rec block b = List.for_all stmt b.bstmts
  and stmt s = match s.skind with
    | Instr ins -> List.for_all (function Set _ | Call _ -> true | _ -> false) ins
    | Return _ -> true
    | If (_, a, b, _) -> block a && block b
    | Block b -> block b
    | _ -> false in
  let rec expression e = match e with
    | CastE (typ, arg) ->
       (match type_of_exp f.sdecls arg with
        | Ok source ->
           let pointer t = is_pointer_type (fenv#get_type_unrolled t) in
           ((pointer typ = pointer source) || (pointer typ && exp_is_zero arg))
           && expression arg
        | _ -> false)
    | Lval lv | AddrOf lv | StartOf lv -> lvalue lv
    | BinOp (_, a, b, _) -> expression a && expression b
    | UnOp (_, a, _) -> expression a
    | Const _ | SizeOf _ | SizeOfE _ | AlignOf _ | AlignOfE _ -> true
    | _ -> false
  and lvalue (host, off) =
    (match host with Var _ -> true | Mem e -> expression e) && offset off
  and offset = function
    | NoOffset -> true
    | Field (_, rest) -> offset rest
    | Index (e, rest) -> expression e && offset rest in
  let rec aliases b = List.for_all (fun st -> match st.skind with
      | Instr ins -> List.for_all (function
          | Set (lv, e, _) -> lvalue lv && expression e
          | Call (lv, fn, args, _) ->
             (match lv with Some lv -> lvalue lv | _ -> true)
             && expression fn && List.for_all expression args
          | _ -> false) ins
      | Return (e, _) -> (match e with Some e -> expression e | _ -> true)
      | If (e, a, b, _) -> expression e && aliases a && aliases b
      | Block b -> aliases b
      | _ -> false) b.bstmts in
  let query = object method fenv = f.sdecls end in
  let conversion target source value =
    let target = fenv#get_type_unrolled target and source = fenv#get_type_unrolled source in
    match target, source with
    | TInt (IBool, _), _ -> false
    | TInt _, TInt _ ->
       let dst = range_of_type f.sdecls target and src = range_of_type f.sdecls source in
       (dst#min#leq src#min && dst#max#geq src#max)
       || (match value with
           | Some e -> (match literal_value query e with
               | Some (XConst (IntConst n)) -> n#geq dst#min && n#leq dst#max
               | _ -> false)
           | _ -> false)
    | TPtr _, TPtr _ -> true
    | TPtr _, TInt _ -> (match value with Some e -> exp_is_zero e | _ -> false)
    | _ -> typ_compare target source = 0 in
  let rec casts e = match e with
    | CastE (target, arg) ->
       (match type_of_exp f.sdecls arg with
        | Ok source -> conversion target source (Some arg) && casts arg
        | _ -> false)
    | Lval lv | AddrOf lv | StartOf lv -> clval lv
    | BinOp (_, a, b, _) -> casts a && casts b
    | UnOp (_, a, _) -> casts a
    | Const _ | SizeOf _ | SizeOfE _ | AlignOf _ | AlignOfE _ -> true
    | _ -> false
  and clval (host, off) =
    (match host with Var _ -> true | Mem e -> casts e) && coff off
  and coff = function
    | NoOffset -> true | Field (_, o) -> coff o | Index (e, o) -> casts e && coff o in
  let status_slot = function
    | Var (_, vid), off ->
       let rec ordinary typ off =
         if is_volatile_type (fenv#get_type_unrolled typ) then false else match off with
         | NoOffset -> not (is_volatile_type (fenv#get_type_unrolled typ))
         | Field ((name, key), rest) ->
            (match fenv#get_type_unrolled typ with
             | TComp (k, _) when k = key && (fenv#get_comp k).cstruct ->
                (match List.find_opt (fun field -> field.fname = name && field.fbitfield = None)
                         (fenv#get_comp k).cfields with
                 | Some field -> ordinary field.ftype rest | _ -> false)
             | _ -> false)
         | _ -> false in
       (match env#get_varinfo vid with
        | Ok vi -> not vi.vglob && ordinary vi.vtype off
                   && (not vi.vaddrof
                       || (off <> NoOffset && vi.vattr = []
                           && readonly_descriptor_address_uses f vi.vid))
        | _ -> false)
    | _ -> false in
  let assign lv source value = match type_of_lval f.sdecls lv with
    | Ok target ->
       (match fenv#get_type_unrolled target with TInt _ -> status_slot lv | _ -> true)
       && conversion target source value
    | _ -> false in
  let guarded_instruction = function
          | Set (lv, e, _) ->
             clval lv && casts e && (match type_of_exp f.sdecls e with
                 | Ok source -> assign lv source (Some e) | _ -> false)
          | Call (lhs, fn, args, _) ->
             casts fn && List.for_all casts args && (match lhs with
               | None -> true
               | Some lv -> clval lv && (match type_of_exp f.sdecls fn with
                   | Ok typ -> (match fenv#get_type_unrolled typ with
                       | TFun (ret, _, _, _) -> assign lv ret None
                       | TPtr (TFun (ret, _, _, _), _) -> assign lv ret None
                       | _ -> false)
                   | _ -> false))
          | _ -> false in
  (* An unsupported conversion invalidates this path, not a sibling path that
     cannot reach the read. Return has no fallthrough. Join the safety of all
     continuing predecessors; never recover safety after a bad conversion.
     Keep alias/control-flow exclusions global. The contexts mirror the
     supported structured translation in cCHCfgTranslator. *)
  let contexts = Hashtbl.create 17 in
  let record ctxt safe =
    Hashtbl.replace contexts ctxt#get_cfg_context#index safe in
  let join a b = match a, b with
    | None, x | x, None -> x
    | Some a, Some b -> Some (a && b) in
  let rec guarded_block ctxt state b =
    List.fold_left (fun state s -> guarded_stmt (ctxt#add_stmt s.sid) state s)
      state b.bstmts
  and guarded_stmt ctxt state s =
    let safe = state = Some true in
    match s.skind with
    | Instr ins ->
       let result = List.fold_left (fun (i, state) ins ->
           let next = state = Some true && guarded_instruction ins in
           record (ctxt#add_instr i) next;
           (i + 1, if state = None then None else Some next)) (0, state) ins in
       snd result
    | Return (e, _) ->
       record ctxt#add_return
         (safe && (match e with Some e -> casts e | _ -> true));
       None
    | If (e, a, b, _) ->
       let next = safe && casts e in
       record ctxt#add_if_expr next;
       let incoming = if state = None then None else Some next in
       join (guarded_block ctxt#add_if_then incoming a)
         (guarded_block ctxt#add_if_else incoming b)
    | Block b -> guarded_block ctxt state b
    | _ -> Some false in
  ignore (guarded_block (CCHContext.mk_program_context ()) (Some true) f.sbody);
  Hashtbl.replace guarded_output_contexts env#get_functionname contexts;
  Hashtbl.replace local_range_enabled env#get_functionname (block f.sbody);
  Hashtbl.replace guarded_outputs_enabled env#get_functionname
    (List.exists (function Attr ("codehawk_nested_scope_metadata_v1", []) -> true | _ -> false)
       f.sbody.battrs && block f.sbody && aliases f.sbody);
  Hashtbl.replace local_alias_enabled env#get_functionname
    (List.exists (function
         | Attr ("codehawk_nested_scope_metadata_v1", []) -> true
         | _ -> false) f.sbody.battrs
     && block f.sbody && aliases f.sbody)

(* Absence of a nested attribute is meaningful only with the parser's scope
   metadata certificate above.  All nested aliases remain unsupported, even
   before block exit: their exact lifetime is not represented by this domain. *)
let function_scope_local vi =
  not vi.vglob && not (List.exists (function
      | Attr ("goblint_cil_nested", _) -> true | _ -> false) vi.vattr)

(* A CIL local declaration alone does not establish a live automatic object:
   nested blocks are flattened, and their addresses can outlive the objects.
   Until declaration/use scopes are represented, accept only fixed-size locals
   in the original function block, certified by the parser.  This deliberately
   leaves even live nested aliases open.  Static storage has function-independent
   lifetime.  Missing metadata must never mean "not nested". *)
let stack_address_lifetime_known (env: c_environment_int) vi =
  vi.vglob || vi.vstorage = Static
  || (function_scope_local vi
      && (match constant (size_of_type env#get_fdecls vi.vtype) with
          | Some n -> n#gt numerical_zero
          | _ -> false)
      && (match Hashtbl.find_opt local_function_bodies env#get_functionname with
          | Some body -> List.exists (function
              | Attr ("codehawk_nested_scope_metadata_v1", []) -> true
              | _ -> false) body.sbody.battrs
          | _ -> false))

let guarded_output_initialization_enabled env =
  Hashtbl.find_opt guarded_outputs_enabled env#get_functionname = Some true

let guarded_return_dependency (poq: po_query_int) ctxt callctxt callee op bound =
  if not (guarded_output_initialization_enabled poq#env) then None else
  if not (match Hashtbl.find_opt guarded_output_contexts poq#env#get_functionname with
      | Some contexts -> Hashtbl.find_opt contexts ctxt#get_cfg_context#index = Some true
      | _ -> false) then None else
  if not (List.for_all (fun g -> g#get_value = None)
      CCHFileContract.file_contract#get_globalvar_contracts) then None else
  let facts = poq#get_context_invariants ctxt in
  let same_return v =
    poq#env#is_function_return_value v
    && (match fenv#get_type_unrolled (poq#env#get_callvar_callee v).vtype with
        | TFun (ret, _, _, _) ->
           (match fenv#get_type_unrolled ret with TInt _ -> true | _ -> false)
        | _ -> false)
    && (poq#env#get_callvar_callee v).vid = callee
    && (CCHContext.ccontexts#index_context (poq#env#get_callvar_context v)) = callctxt in
  let satisfies low high =
    let lower p = match low with Some n -> p n | _ -> false in
    let upper p = match high with Some n -> p n | _ -> false in
    match op with
    | Ge -> lower (fun n -> n#geq bound)
    | Gt -> lower (fun n -> n#gt bound)
    | Le -> upper (fun n -> n#leq bound)
    | Lt -> upper (fun n -> n#lt bound)
    | Eq -> lower (fun n -> n#equal bound) && upper (fun n -> n#equal bound)
    | Ne -> lower (fun n -> n#gt bound) || upper (fun n -> n#lt bound)
    | _ -> false in
  List.find_map (fun (binding: invariant_int) -> match binding#get_fact with
      | NonRelationalFact (slot, FSymbolicExpr (XVar v)) when same_return v ->
         List.find_map (fun (range: invariant_int) -> match range#get_fact with
             | NonRelationalFact (other, FIntervalValue (low, high))
                  when other#equal slot && satisfies low high ->
                Some [binding#index; range#index]
             | _ -> None) facts
      | NonRelationalFact (v, FIntervalValue (low, high))
           when same_return v && satisfies low high -> Some [binding#index]
      | _ -> None) facts

let rec local_address_root = function
  | CastE (typ, e) when is_pointer_type typ -> local_address_root e
  | AddrOf (Var (_, vid), _) | StartOf (Var (_, vid), _) -> Some vid
  | BinOp ((PlusPI | MinusPI | IndexPI), e, _, _) -> local_address_root e
  | _ -> None

let byte_ranges_written (env: c_environment_int) = function
  | Var (_, vid), _ ->
     (match List.find_opt (fun vi -> vi.vid = vid) env#get_fdecls#get_locals with
      | Some vi -> [local_byte_range_variable env vi]
      | _ -> [])
  | Mem e, _ ->
     (match local_address_root e with
      | Some vid ->
         (match List.find_opt (fun vi -> vi.vid = vid) env#get_fdecls#get_locals with
          | Some vi -> [local_byte_range_variable env vi]
          | _ -> [])
      | _ -> local_byte_range_variables env)

let byte_ranges_written_at env address = byte_ranges_written env (Mem address, NoOffset)

let rec range_type_volatile seen typ =
  let typ = fenv#get_type_unrolled typ in
  is_volatile_type typ || match typ with
    | TArray (elem, _, _) -> range_type_volatile seen elem
    | TComp (key, _) when not (List.mem key seen) ->
       List.exists (fun f -> range_type_volatile (key :: seen) f.ftype)
         (fenv#get_comp key).cfields
    | _ -> false

(* A full clear covers nested subobjects without guessing structure layout.
   Partial intervals use only offsets whose byte position is already known
   (constant array indices/union members). Padding and bitfields are never
   inferred from ordinary field assignments. *)
let rec contained_subobject poq typ off = match off with
  | NoOffset -> Some typ
  | Field ((name, key), rest) ->
     (match fenv#get_type_unrolled typ with
      | TComp (k, _) when k = key ->
         (match List.find_opt (fun f -> f.fname = name && f.fbitfield = None)
                  (fenv#get_comp k).cfields with
          | Some field -> contained_subobject poq field.ftype rest
          | _ -> None)
      | _ -> None)
  | Index (e, rest) ->
     (match fenv#get_type_unrolled typ, literal_value poq e with
      | TArray (elem, _, _), Some (XConst (IntConst i)) ->
         (match sizeof poq typ, sizeof poq elem with
          | Some sz, Some esz when i#geq numerical_zero && esz#gt numerical_zero
                                  && ((i#add numerical_one)#mult esz)#leq sz ->
             contained_subobject poq elem rest
          | _ -> None)
      | _ -> None)


(* Numeric values are used only for unaddressed local slots and ordinary
   structure/array fields. Escaped slots, globals, union views and pointer/int
   conversions may retain representation/alias facts that cannot establish an
   exact address here. Nonzero numeric pointer arithmetic is never rescaled. *)
let safe_alias_slot (env: c_environment_int) lv =
  let rec path typ = function
    | NoOffset -> not (range_type_volatile [] typ)
    | Field ((name, key), rest) ->
       (match fenv#get_type_unrolled typ with
        | TComp (k, _) when k = key && (fenv#get_comp k).cstruct ->
           (match List.find_opt (fun f -> f.fname = name && f.fbitfield = None)
                    (fenv#get_comp k).cfields with
            | Some f -> path f.ftype rest | _ -> false)
        | _ -> false)
    | Index (Const (CInt (i, _, _)), rest) when i >= 0L ->
       (match fenv#get_type_unrolled typ with TArray (elem, _, _) -> path elem rest | _ -> false)
    | _ -> false in
  Hashtbl.find_opt local_alias_enabled env#get_functionname = Some true
  && List.for_all (fun g -> g#get_value = None)
       CCHFileContract.file_contract#get_globalvar_contracts
  && match lv with
     | Var (_, vid), off ->
        (match env#get_varinfo vid with
         | Ok vi -> function_scope_local vi && not vi.vaddrof
                    && not (range_type_volatile [] vi.vtype) && path vi.vtype off
         | _ -> false)
     | _ -> false

(* A descriptor's address may be exposed solely to a modeled read-only getter
   returning an ordinary pointer or integer field. Do not reuse numeric field facts for
   arbitrary escaped descriptors: byte writes, root-alias returns, opaque
   calls and union views can otherwise leave stale overlapping values. *)
let readonly_getter_field (env: c_environment_int) argument soff =
  let contracts = CCHFileContract.file_contract in
  let rec root = function
    | CastE (typ, e) when is_pointer_type (fenv#get_type_unrolled typ) -> root e
    | AddrOf (Var (_, vid), NoOffset) -> Some vid
    | _ -> None in
  match root argument, Hashtbl.find_opt local_function_bodies env#get_functionname with
  | Some vid, Some body when
      Hashtbl.find_opt local_alias_enabled env#get_functionname = Some true
      && List.for_all (fun g -> g#get_value = None) contracts#get_globalvar_contracts ->
     (match env#get_varinfo vid with
      | Ok vi when function_scope_local vi && readonly_descriptor_address_uses body vid ->
         let rec select typ off =
           let typ = fenv#get_type_unrolled typ in
           if is_volatile_type typ then None else match off with
             | ArgFieldOffset (name, rest) ->
                (match typ with
                 | TComp (key, _) when (fenv#get_comp key).cstruct ->
                    (match List.find_opt (fun f -> f.fname = name && f.fbitfield = None)
                             (fenv#get_comp key).cfields with
                     | Some field -> Option.map (fun tail -> Field ((name, key), tail))
                         (select field.ftype rest)
                     | _ -> None)
                 | _ -> None)
             | ArgNoOffset when is_pointer_type typ -> Some NoOffset
             | ArgNoOffset -> (match typ with TInt (kind, _) when kind <> IBool -> Some NoOffset | _ -> None)
             | _ -> None in
         Option.map (fun off -> Lval (Var (vi.vname, vi.vid), off)) (select vi.vtype soff)
      | _ -> None)
  | _ -> None

(* Scalar equality transport must not silently narrow/reinterpret a field.
   Pointer qualifiers retain the existing exact-address policy. No floating,
   Boolean, enum, aggregate or mixed-width integer field is transported. *)
let readonly_getter_result_field env argument soff returntype =
  Option.bind (readonly_getter_field env argument soff) (fun field ->
      match type_of_exp env#get_fdecls field with
      | Ok typ -> (match fenv#get_type_unrolled typ, fenv#get_type_unrolled returntype with
          | TPtr _, TPtr _ -> Some field
          | TInt (a, _), TInt (b, _) when a = b && a <> IBool -> Some field
          | _ -> None)
      | _ -> None)

let exact_local_address (env: c_environment_int) = function
  | XVar v when env#is_memory_address v ->
     let (memref, off) = env#get_memory_address v in
     (match memref#get_base with
      | CStackAddress stack when env#is_local_variable stack ->
         let (vi, baseoff) = env#get_local_variable stack in
         if not (function_scope_local vi) then None else
           Some ((Var (vi.vname, vi.vid), add_offset baseoff off), numerical_zero)
      | _ -> None)
  | _ -> None

let resolve_local_region (env: c_environment_int) get_value address =
  let query = object method fenv = env#get_fdecls end in
  let rec resolve = function
    | CastE (typ, e) when is_pointer_type (fenv#get_type_unrolled typ) -> resolve e
    | AddrOf ((Var _, _) as lv) | StartOf ((Var _, _) as lv) -> Some (lv, numerical_zero)
    | Lval lv as e when safe_alias_slot env lv ->
       (match type_of_lval env#get_fdecls lv with
        | Ok typ when is_pointer_type (fenv#get_type_unrolled typ) ->
           Option.bind (get_value e) (exact_local_address env)
        | _ -> None)
    | BinOp ((PlusPI | IndexPI), base, index, _) ->
       (match resolve base, literal_value query index,
              get_pointer_expr_target_type env#get_fdecls base with
        | Some (lv, first), Some (XConst (IntConst i)), Ok elem when i#geq numerical_zero ->
           (match constant (size_of_type env#get_fdecls elem) with
            | Some n when n#gt numerical_zero -> Some (lv, first#add (i#mult n))
            | _ -> None)
        | _ -> None)
    | AddrOf (Mem base, off) | StartOf (Mem base, off) ->
       (match resolve base, get_pointer_expr_target_type env#get_fdecls base with
        | Some (lv, first), Ok _ when off = NoOffset -> Some (lv, first)
        | Some (lv, first), Ok pointed ->
           (match type_of_lval env#get_fdecls lv with
            | Ok typ ->
               let typ = fenv#get_type_unrolled typ in
               let pointed = fenv#get_type_unrolled pointed in
               let select anchor = match anchor with
                 | (Var (_, vid), offset) ->
                    (match env#get_varinfo vid with
                     | Ok vi ->
                        let alloff = add_offset offset off in
                        (* Full byte proof checks the complete object path. *)
                        Some ((Var (vi.vname, vi.vid), alloff), numerical_zero)
                     | _ -> None)
                 | _ -> None in
               (match typ, constant (size_of_type env#get_fdecls pointed) with
                | TArray (elem, _, _), Some sz when sz#gt numerical_zero
                    && typ_compare (fenv#get_type_unrolled elem) pointed = 0
                    && first#geq numerical_zero && (first#modulo sz)#equal numerical_zero ->
                   let host, offset = lv in
                   select (host, add_offset offset (mk_constant_index_offset (first#div sz)))
                | _ when first#equal numerical_zero && typ_compare typ pointed = 0 -> select lv
                | _ -> None)
            | _ -> None)
        | _ -> None)
    | _ -> None in
  resolve address

let exact_local_length (env: c_environment_int) get_value expression =
  let query = object method fenv = env#get_fdecls end in
  let rec value e = match literal_value query e with
    | Some _ as result -> result
    | _ -> (match e with
        | Lval lv when safe_alias_slot env lv ->
           (match get_value e with Some (XConst (IntConst _) as x) -> Some x | _ -> None)
        | CastE (typ, source) ->
           (match fenv#get_type_unrolled typ, value source with
            | TInt (kind, _), Some (XConst (IntConst n)) when kind <> IBool ->
               let range = range_of_type env#get_fdecls typ in
               if n#geq range#min && n#leq range#max then Some (XConst (IntConst n)) else None
            | _ -> None)
        | _ -> None) in
  value expression

let context_local_value (poq: po_query_int) ctxt = function
  | Lval ((Var (_, vid), off) as lv) when safe_alias_slot poq#env lv ->
     (match poq#env#get_varinfo vid with
      | Ok vi ->
         let v = poq#env#mk_program_var vi off CHLanguage.NUM_VAR_TYPE in
         List.find_map (fun (inv: invariant_int) -> if inv#applies_to_var v then
             match inv#expr with
             | Some ((XVar _ | XConst (IntConst _)) as x) -> Some x
             | _ -> None else None) (poq#get_context_invariants ctxt)
      | _ -> None)
  | _ -> None

(* Supported allocation origins are captured only within acyclic functions.
   Literal capacity belongs to the original malloc call or guarded output
   contract, never a later descriptor. Zero/dynamic sizes remain unsupported. *)
let allocated_origin (env: c_environment_int) value =
  let root = match value with
    | XVar v when env#is_function_return_value v -> Some v
    | XVar v when env#is_memory_address v ->
       (match env#get_memory_address v with
        | mem, NoOffset -> (match mem#get_base with CBaseVar (v, _) -> Some v | _ -> None)
        | _ -> None)
    | XVar v when env#is_fixed_value v -> Some v
  | _ -> None in
  match root with
  | Some v when Option.is_some (guarded_buffer_origin env v) ->
     Option.map (fun (_, capacity, _) -> v, capacity) (guarded_buffer_origin env v)
  | Some v when env#is_function_return_value v
                && Hashtbl.find_opt local_alias_enabled env#get_functionname = Some true ->
     let ctxt = env#get_callvar_context v in
     if proof_scaffolding#has_direct_callsite env#get_functionname ctxt then
       let call = proof_scaffolding#get_direct_callsite env#get_functionname ctxt in
       if call#get_header = "lib:stdlib" && call#get_callee.vname = "malloc" then
         (match env#get_callvar_args v with
          | [Some (XConst (IntConst n))] when n#gt numerical_zero -> Some (v, n)
          | _ -> None)
       else None
     else None
  | _ -> None

(* Unknown structure layout is represented by a covering object, not a guessed
   field offset. A proof then requires the entire enclosing object initialized.
   Leaf size still bounds the actual request. Partial structure intervals may
   lose precision; complete allocation clears cover bounded fields. *)
let resolve_allocated_region (env: c_environment_int) get_value address =
  let query = object method fenv = env#get_fdecls end in
  let rec resolve = function
    | CastE (typ, e) when is_pointer_type (fenv#get_type_unrolled typ) -> resolve e
    | Lval lv as e when safe_alias_slot env lv ->
       Option.bind (get_value e) (fun x -> Option.map (fun (v, n) ->
           (v, n, numerical_zero, None, None)) (allocated_origin env x))
    | BinOp ((PlusPI | IndexPI), base, index, _) ->
       (match resolve base, literal_value query index,
              get_pointer_expr_target_type env#get_fdecls base with
        | Some (v, n, first, None, None), Some (XConst (IntConst i)), Ok typ
             when i#geq numerical_zero ->
           Option.bind (sizeof query typ) (fun size ->
               if size#gt numerical_zero then
                 Some (v, n, first#add (i#mult size), None, None) else None)
        | _ -> None)
    | AddrOf (Mem base, off) | StartOf (Mem base, off) ->
       (match resolve base with
        | Some _ as r when off = NoOffset -> r
        | Some (v, n, first, None, None) ->
           (match get_pointer_expr_target_type env#get_fdecls base with
            | Ok typ ->
               (match sizeof query typ, contained_subobject query typ off with
                | Some span, Some leaf -> Option.map (fun width ->
                    (v, n, first, Some span, Some width)) (sizeof query leaf)
                | _ -> None)
            | _ -> None)
        | _ -> None)
    | _ -> None in
  resolve address

let memset_allocated_byte_range (env: c_environment_int) get_value args =
  match args with
  | [dest; _; len] ->
     (match resolve_allocated_region env get_value dest, exact_local_length env get_value len with
      | Some (v, capacity, first, None, None), Some (XConst (IntConst count))
           when first#geq numerical_zero && count#gt numerical_zero
                && (first#add count)#leq capacity ->
         let marker = new CHLanguage.symbol_t
             ~atts:[first#toString; count#toString] "allocated-memset-bytes" in
         [CCHCommand.make_c_cmd (CHLanguage.ASSIGN_SYM
             (allocated_byte_range_variable env (allocation_context env v), CHLanguage.SYM marker))]
      | _ -> [])
  | _ -> []

let prove_allocated_bytes (poq: po_query_int) ctxt address count =
  let facts = poq#get_context_invariants ctxt in
  let aliases = ref [] in
  let value e =
    let result = context_local_value poq ctxt e in
    (match e, result with
     | Lval (Var (_, vid), off), Some _ ->
        (match poq#env#get_varinfo vid with
         | Ok vi ->
            let slot = poq#env#mk_program_var vi off CHLanguage.NUM_VAR_TYPE in
            List.iter (fun (inv: invariant_int) ->
                if inv#applies_to_var slot then aliases := inv#index :: !aliases) facts
         | _ -> ())
     | _ -> ());
    result in
  match resolve_allocated_region poq#env value address with
  | Some (v, capacity, first, span, leaf)
       when first#geq numerical_zero && count#gt numerical_zero
            && (match leaf with Some width -> count#leq width | _ -> true) ->
     let width = match span with Some n -> n | _ -> count in
     if (first#add width)#gt capacity then None else
     let permission = match guarded_buffer_origin poq#env v with
       | Some (call, _, (XBufferOnReturn (op, bound, _, _) as predicate)) ->
          Option.map (fun guard -> guard, [PostAssumption (call#get_callee.vid, predicate)])
            (guarded_return_dependency poq ctxt
               (CCHContext.ccontexts#index_context call#get_context) call#get_callee.vid op bound)
       | Some _ -> None
       | _ ->
          (* malloc needs a nonnull value-set fact for the exact captured base. *)
          let origins = List.filter_map (fun (inv: invariant_int) -> match inv#get_fact with
              | NonRelationalFact (_, FBaseOffsetValue (_, base, Some a, Some b, false))
                   when a#equal numerical_zero && b#equal numerical_zero ->
                 (match allocated_origin poq#env base with
                  | Some (other, _) when other#equal v -> Some inv#index
                  | _ -> None)
              | _ -> None) facts in
          let pcs, _ = poq#get_postconditions v in
          if origins = [] || not (List.exists (fun (p, _) -> p = XNewMemory ReturnValue) pcs)
          then None else
          (match poq#get_function_return_value_buffer_size v with
           | Some (assumptions, XConst (IntConst n)) when n#equal capacity ->
              let callee = poq#env#get_callvar_callee v in
              Some (origins, PostAssumption (callee.vid, XNewMemory ReturnValue) :: assumptions)
           | _ -> None) in
     let livevar = allocated_live_variable poq#env (allocation_context poq#env v) in
     let live = List.find_opt (fun (inv: invariant_int) -> match inv#get_fact with
         | NonRelationalFact (var, FInitializedSet syms) when var#equal livevar ->
            syms <> [] && List.for_all (fun s ->
                s#getBaseName = "allocated-live" && s#getAttributes = []) syms
         | _ -> false) facts in
     (match permission, live with
      | Some (origins, assumptions), Some live ->
         let variable = allocated_byte_range_variable poq#env (allocation_context poq#env v) in
         List.find_map (fun (inv: invariant_int) -> match inv#get_fact with
             | NonRelationalFact (var, FInitializedSet syms) when var#equal variable && syms <> [] ->
                let covers s = match s#getBaseName, s#getAttributes with
                  | "allocated-memset-bytes", [a; b] ->
                     (try let a = mkNumericalFromString a and b = mkNumericalFromString b in
                          a#geq numerical_zero && b#gt numerical_zero
                          && (a#add b)#leq capacity && first#geq a
                          && (first#add width)#leq (a#add b) with _ -> false)
                  | _ -> false in
                if List.for_all covers syms then
                  Some (DEnvC (inv#index :: live#index :: (origins @ !aliases), assumptions))
                else None
             | _ -> None) facts
      | _ -> None)
  | _ -> None

let memset_local_byte_range (env: c_environment_int) get_value args =
  if Hashtbl.find_opt local_range_enabled env#get_functionname <> Some true then [] else
  match args with
  | [dest; _; len] ->
     (match resolve_local_region env get_value dest, exact_local_length env get_value len with
      | Some (((Var (_, vid), off) as lv), first), Some (XConst (IntConst n)) ->
         (match List.find_opt (fun vi -> vi.vid = vid && not vi.vglob)
                  env#get_fdecls#get_locals, type_of_lval env#get_fdecls lv with
          | Some vi, Ok typ when not (range_type_volatile [] vi.vtype)
                                 && first#geq numerical_zero && n#geq numerical_zero ->
             (match constant (size_of_type env#get_fdecls typ) with
              | Some size when (first#add n)#leq size ->
                 let marker = new CHLanguage.symbol_t
                     ~atts:[string_of_int (CCHDictionary.cdictionary#index_offset off);
                            first#toString; n#toString] "memset-initialized-bytes" in
                 [CCHCommand.make_c_cmd (CHLanguage.ASSIGN_SYM
                    (local_byte_range_variable env vi, CHLanguage.SYM marker))]
              | _ -> [])
          | _ -> [])
      | _ -> [])
  | _ -> []


let prove_cleared_local_bytes (poq: po_query_int) ctxt (lv: lval) start count =
  match lv with
  | Var (_, vid), off ->
     (match poq#env#get_varinfo vid with
      | Ok vi when not vi.vglob && not (range_type_volatile [] vi.vtype) ->
         let variable = local_byte_range_variable poq#env vi in
         let covers sym =
           match sym#getBaseName, sym#getAttributes with
           | "memset-initialized-bytes", [offset; first; length] ->
              (try
                 let baseoff = CCHDictionary.cdictionary#get_offset (int_of_string offset) in
                 let first = mkNumericalFromString first in
                 let length = mkNumericalFromString length in
                 match contained_subobject poq vi.vtype baseoff,
                       offset_suffix baseoff off with
                 | Some basetyp, Some tail ->
                    (match contained_subobject poq basetyp tail, sizeof poq basetyp with
                     | Some typ, Some total ->
                        (match sizeof poq typ with
                         | Some width when start#geq numerical_zero
                             && count#geq numerical_zero && (start#add count)#leq width ->
                            if first#equal numerical_zero && length#equal total then true
                            else (match relative_bytes poq basetyp tail with
                              | Some position ->
                                 let position = position#add start in
                                 position#geq first && (position#add count)#leq (first#add length)
                              | _ -> false)
                         | _ -> false)
                     | _ -> false)
                 | _ -> false
               with Failure _ | Invalid_argument _ -> false)
           | _ -> false in
         let inv = List.find_opt (fun inv -> match inv#get_fact with
             | NonRelationalFact (v, FInitializedSet syms) ->
                v#equal variable && syms <> [] && List.for_all covers syms
             | _ -> false) (poq#get_context_invariants ctxt) in
         (match inv with
          | Some inv ->
             (* Overapproximate frame dependencies by retaining every explicit
                effects contract used anywhere in this function. Even an unused
                frame makes this conditional; no model is silently trusted. *)
             let contracts = CCHFileContract.file_contract in
             let frames = List.concat_map (fun call ->
                 let callee = call#get_callee in
                 if contracts#has_function_contract callee.vname then
                   let contract = contracts#get_function_contract callee.vname in
                   let getter_aliases = List.filter (function
                       | XRelationalExpr (Eq, ReturnValue, ArgAddressedValue _)
                         | XRelationalExpr (Eq, ArgAddressedValue _, ReturnValue) -> true
                       | _ -> false) contract#get_postconditions in
                   List.map (fun p -> PostAssumption (callee.vid, p))
                     (contract#get_sideeffects @ getter_aliases)
                 else []) (proof_scaffolding#get_direct_callsites poq#fname) in
             Some (if frames = [] then DLocal [inv#index]
                   else DEnvC ([inv#index], frames))
          | _ -> None)
      | _ -> None)
  | _ -> None

let assigned (inv: invariant_int) =
  match inv#get_fact with
  | NonRelationalFact (_, FInitializedSet syms) ->
     syms <> [] && List.for_all (fun s ->
         let name = s#getBaseName in
         String.length name >= 11 && String.sub name 0 11 = "assignedAt#"
         && s#getAttributes = []) syms
  | _ -> false

let initialized_local_bytes ?(start=numerical_zero) (poq: po_query_int) ctxt (lv: lval) count =
  match lv with
  | Var (_, vid), offset ->
     (match poq#env#get_varinfo vid with
      | Ok vi when not vi.vglob ->
         let facts = poq#get_context_invariants ctxt in
         let initialized off =
           let memory = poq#env#mk_stack_memory_variable vi off vi.vtype
               CHLanguage.SYM_VAR_TYPE in
           List.find_opt (fun inv ->
               assigned inv &&
                 match inv#get_fact with
                 | NonRelationalFact (v, _) ->
                    v#equal memory || (match poq#env#get_vinfo_offset v vi with
                     | Some o -> offset_compare o off = 0
                     | _ -> false)
                 | _ -> false) facts in
         let rec prove typ off first len =
           if len#equal numerical_zero then Some (DLocal []) else
             match fenv#get_type_unrolled typ, sizeof poq typ with
             | (TInt _ | TFloat ((FFloat | FDouble), _)), Some sz
                  when first#geq numerical_zero && len#gt numerical_zero
                       && (first#add len)#leq sz ->
                (match initialized off with
                 | Some inv -> Some (DLocal [inv#index])
                 | _ -> None)
             | TComp (key, _), Some sz
                  when first#geq numerical_zero && (first#add len)#leq sz ->
                let comp = fenv#get_comp key in
                if comp.cstruct then None else
                  List.fold_left (fun acc field ->
                      match acc, field.fbitfield with
                      | Some _, _ -> acc
                      | _, Some _ -> None
                      | _ -> prove field.ftype
                          (add_offset off (Field ((field.fname, key), NoOffset))) first len)
                    None comp.cfields
             | TArray (elem, _, _), Some sz
                  when first#geq numerical_zero && (first#add len)#leq sz ->
                (match sizeof poq elem with
                 | Some esz when esz#gt numerical_zero ->
                    let rec elements index skip remaining deps =
                      if remaining#leq numerical_zero then Some deps else
                        let available = esz#sub skip in
                        let part = if remaining#lt available then remaining else available in
                        match prove elem
                                (add_offset off (mk_constant_index_offset index)) skip part with
                        | Some d -> elements (index#add numerical_one) numerical_zero
                            (remaining#sub part) (join_dependencies deps d)
                        | _ -> None in
                    elements (first#div esz) (first#modulo esz) len (DLocal [])
                 | _ -> None)
             | _ -> None in
         (match local_type poq lv with
          | Some typ when count#geq numerical_zero ->
             let result = match prove typ offset start count with
               | Some _ as result -> result
               | _ -> prove_cleared_local_bytes poq ctxt lv start count in
             let _ = poq#set_key_diagnostic "copy-source-size"
                 (vi.vname ^ ": byte offset " ^ start#toString
                  ^ "; requested bytes " ^ count#toString ^ "; type size: " ^
                    (match sizeof poq typ with Some n -> n#toString | _ -> "unknown")) in
             result
          | _ -> None)
      | _ -> None)
  | _ -> None

let addressed_source_at (poq: po_query_int) ctxt expression =
  match addressed_source poq expression with
  | Some _ as result -> result
  | _ -> resolve_local_region poq#env (context_local_value poq ctxt) expression

let prove_initialized_range poq ctxt address length =
  match addressed_source_at poq ctxt address,
        exact_local_length poq#env (context_local_value poq ctxt) length with
  | Some (lv, start), Some x ->
     (match constant x with
      | Some n -> initialized_local_bytes ~start poq ctxt lv n
      | _ -> None)
  | _ ->
     (match exact_local_length poq#env (context_local_value poq ctxt) length with
      | Some (XConst (IntConst n)) -> prove_allocated_bytes poq ctxt address n
      | _ -> None)

let memcpy_call poq sequence =
  let origin = poq#env#get_byte_sequence_origin sequence in
  let callee = poq#env#get_callvar_callee origin in
  let ctxt = poq#env#get_callvar_context origin in
  if callee.vname = "memcpy"
     && proof_scaffolding#has_direct_callsite poq#fname ctxt then
    let call = proof_scaffolding#get_direct_callsite poq#fname ctxt in
    if call#get_header = "lib:string" then Some (origin, call) else None
  else None

let prove_memcpy_read poq sequence (read: lval) =
  match memcpy_call poq sequence with
  | Some (origin, call) ->
     (match call#get_arguments with
      | [dest; source; length] ->
         let len =
           match poq#env#get_callvar_args origin with
           | [_; _; Some x] -> constant x
           | _ ->
              (match literal_value poq length with
               | Some x -> constant x | _ -> None) in
         (match addressed_local dest, len, read with
          | Some ((Var (_, dvid), doff) as dlv), Some n,
            (Var (_, rvid), roff) when dvid = rvid ->
             (match local_type poq dlv, local_type poq read,
                    offset_suffix doff roff with
              | Some dtyp, Some ((TInt _ | TFloat ((FFloat | FDouble), _)) as rtyp),
                Some tail ->
                 (match relative_bytes poq dtyp tail, sizeof poq rtyp with
                  | Some start, Some width when (start#add width)#leq n ->
                     (let source_bytes = match addressed_source_at poq call#get_context source with
                        | Some (slv, sstart) -> initialized_local_bytes ~start:sstart poq call#get_context slv n
                        | _ -> prove_allocated_bytes poq call#get_context source n in
                      match source_bytes with
                      | Some deps -> Some (deps,
                          "memcpy source bytes initialized at call; copied "
                          ^ n#toString ^ " bytes cover destination read")
                      | _ -> None)
                  | _ -> None)
              | _ -> None)
          | _ -> None)
      | _ -> None)
  | _ -> None
