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
let exact_count_contexts : (string, (int, bool) Hashtbl.t) Hashtbl.t =
  Hashtbl.create 17

type byte_capacity_t =
  | ConstantCapacity of numerical_t
  | ArgumentCapacity of program_context_int * exp

let unsigned_count_kind (env: c_environment_int) = function
  | Lval (Var (_, vid), NoOffset) ->
     (match env#get_varinfo vid with
      | Ok vi when not vi.vglob && not vi.vaddrof && vi.vstorage <> Static && vi.vattr = [] ->
         (match fenv#get_type_unrolled vi.vtype with
          | TInt (kind, _) as typ when kind <> IBool && is_unsigned_type kind
                                       && not (is_volatile_type typ) -> Some kind
          | _ -> None)
      | _ -> None)
  | _ -> None

(* A count argument with the same integral kind as its formal needs no
   modeled argument conversion. *)
let unsigned_count_argument (env: c_environment_int) (call: direct_callsite_int) index =
  if index < 1 then None else
  match List.nth_opt call#get_arguments (index - 1),
        fenv#get_type_unrolled call#get_callee.vtype with
  | Some arg, TFun (_, Some formals, _, _) ->
     (match unsigned_count_kind env arg, List.nth_opt formals (index - 1) with
      | Some actual, Some (_, formal, _) ->
         (match fenv#get_type_unrolled formal with
          | TInt (expected, _) when actual = expected -> Some arg
          | _ -> None)
      | _ -> None)
  | _ -> None

(* A guarded output region is a value captured at one acyclic call site.
   It is not a malloc return, nor a claim of fresh/disjoint physical storage.
   It requires an actual function-scope void* output slot. Capacity is either
   a positive constant or the by-value unsigned count at the allocation call.
   Casts do not change the actual output slot's C type. *)
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
       | NumConstant n when n#gt numerical_zero -> Some (ConstantCapacity n)
       | ArgValue (ParFormal m, ArgNoOffset) ->
          (match Option.bind (argument m) (literal_value query) with
           | Some (XConst (IntConst n)) when n#gt numerical_zero -> Some (ConstantCapacity n)
           | _ -> Option.map (fun e -> ArgumentCapacity (call#get_context, e))
                    (unsigned_count_argument env call m))
       | _ -> None in
     (match Option.bind (argument n) slot, capacity with
      | Some (vi, off), Some capacity ->
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

type setter_value_t =
  | SetterArgument of int
  | SetterLiteral of exp

(* Only a same-translation-unit static definition can establish the setter's
   complete behavior here. This fragment writes ordinary fields of its first
   formal from by-value scalar arguments or integer literals, then returns. *)
let descriptor_setters :
    (int, (int * typ list * (offset * setter_value_t) list) option) Hashtbl.t =
  Hashtbl.create 17

let static_definitions = Hashtbl.create 17

let reset_descriptor_setters file =
  Hashtbl.clear descriptor_setters;
  Hashtbl.clear static_definitions;
  List.iter (function
      | GFun (vi, _) when vi.vstorage = Static -> Hashtbl.replace static_definitions vi.vid ()
      | _ -> ()) file.globals

let scalar_field_type t =
  let t = fenv#get_type_unrolled t in
  let qualifiers = List.for_all (function Attr ("const", []) -> true | _ -> false) in
  match t with
     | TInt (kind, attrs) -> kind <> IBool && qualifiers attrs
     | TPtr (_, attrs) -> qualifiers attrs
     | _ -> false

let same_setter_type a b =
  let a = fenv#get_type_unrolled a and b = fenv#get_type_unrolled b in
  scalar_field_type a && scalar_field_type b
  && match a, b with
     | TInt (i, _), TInt (j, _) -> i = j
     | TPtr _, TPtr _ -> typ_compare a b = 0
     | _ -> false

let get_descriptor_setter name vid =
  match Hashtbl.find_opt descriptor_setters vid with
  | Some result -> result
  | _ ->
     let result =
       match fenv#get_globalvar vid with
       | Ok vi when vi.vname = name && vi.vstorage = Static
                    && vi.vattr = []
                    && Hashtbl.mem static_definitions vid
                    && not (CCHFileContract.file_contract#has_function_contract name) ->
          (match fenv#get_type_unrolled vi.vtype with
           | TFun (TVoid _, Some ((_, TPtr (obj, _), _) :: _), false, _) ->
              (match fenv#get_type_unrolled obj with
               | TComp (key, []) when (fenv#get_comp key).cstruct && (fenv#get_comp key).cattr = [] ->
                  let f = CCHPreFileIO.read_function_semantics name in
                  let formals = List.sort (fun a b -> Int.compare a.vparam b.vparam)
                      f.sdecls#get_formals in
                  (match formals with
                   | dst :: formals when dst.vparam = 1 && f.svar.vid = vid && f.sdecls#get_locals = []
                         && List.for_all (fun v -> v.vattr = [] && scalar_field_type v.vtype) formals ->
                      let indexed = List.mapi (fun i v -> i, v) formals in
                      let field offset =
                        match offset with
                        | Field ((member, k), NoOffset) when key = k ->
                           List.find_opt (fun f -> f.fname = member && f.fbitfield = None
                               && f.fattr = [] && scalar_field_type f.ftype) (fenv#get_comp key).cfields
                        | _ -> None in
                      let value t rhs =
                        match rhs with
                        | Lval (Var (_, id), NoOffset) ->
                           List.find_map (fun (i, v) ->
                               if v.vid = id && v.vattr = [] && same_setter_type v.vtype t
                               then Some (SetterArgument i) else None) indexed
                        | _ ->
                           let query = object method fenv = f.sdecls end in
                           (match fenv#get_type_unrolled t, literal_value query rhs with
                            | TInt _, Some (XConst (IntConst n)) ->
                               let range = range_of_type f.sdecls t in
                               if n#geq range#min && n#leq range#max
                               then Some (SetterLiteral rhs) else None
                            | _ -> None) in
                      let instruction = function
                        | Set ((Mem (Lval (Var (_, id), NoOffset)), off), rhs, _) when id = dst.vid ->
                           Option.bind (field off) (fun f ->
                               Option.map (fun v -> off, v) (value f.ftype rhs))
                        | _ -> None in
                      let rec writes acc = function
                        | [] | [{skind = Return (None, _); _}] -> Some (List.rev acc)
                        | {skind = Instr ins; _} :: rest ->
                           let fields = List.filter_map instruction ins in
                           if List.length fields = List.length ins
                           then writes (List.rev_append fields acc) rest else None
                        | _ -> None in
                      (match writes [] f.sbody.bstmts with
                       | Some (_ :: _ as fields) ->
                          Some (key, List.map (fun v -> v.vtype) formals, fields)
                       | _ -> None)
                   | _ -> None)
               | _ -> None)
           | _ -> None)
       | _ -> None in
     Hashtbl.replace descriptor_setters vid result;
     result

(* Scalar actuals refer only to separate ordinary variables or literals. They
   can be substituted without reevaluating an alias after the first store. *)
let local_setter_assignments fdecls name vid args =
  match args with
  | AddrOf (Var (_, id), NoOffset) :: values ->
     (match fdecls#get_varinfo_by_vid id, get_descriptor_setter name vid with
      | Ok local, Some (key, types, fields)
           when not local.vglob && local.vparam = 0
                && local.vstorage <> Static && local.vattr = [] ->
         (match fenv#get_type_unrolled local.vtype with
          | TComp (k, []) when k = key ->
             let query = object method fenv = fdecls end in
             let scalar typ = function
               | Lval (Var (_, id), NoOffset) ->
                  (match fdecls#get_varinfo_by_vid id with
                   | Ok vi -> not vi.vglob && vi.vattr = [] && same_setter_type vi.vtype typ
                   | _ -> false)
               | e ->
                  (match type_of_exp fdecls e, literal_value query e with
                   | Ok t, Some (XConst (IntConst _)) -> same_setter_type t typ
                   | _ -> false) in
             if List.length types <> List.length values || not (List.for_all2 scalar types values)
             then None else
               let assignments = List.map (fun (off, value) ->
                   let e = match value with
                     | SetterArgument i -> List.nth values i
                     | SetterLiteral e -> e in
                   ((Var (local.vname, id), off), e)) fields in
               Some (id, assignments)
          | _ -> None)
      | _ -> None)
  | _ -> None

(* A local descriptor address may occur only as the complete argument of a
   modeled read-only field getter or a source-checked setter. *)
let descriptor_address_is_confined body vid =
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
       | Lval lv | AddrOf lv | StartOf lv -> lvalue lv
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
                let local_setter = match lhs, fn, args with
                  | None, Lval (Var (name, fnid), NoOffset), AddrOf (Var (_, id), NoOffset) :: _
                       when id = vid ->
                     Option.is_some (local_setter_assignments body.sdecls name fnid args)
                  | _ -> false in
                (match lhs with None -> true | Some lv -> lvalue lv)
                && expression false fn
                && List.for_all (fun (i, arg) ->
                    let allowed = match fn with
                      | Lval (Var (name, _), NoOffset) -> (i = 0 && local_setter) || getter_argument name (i + 1)
                      | _ -> false in
                    expression allowed arg) (List.mapi (fun i x -> i, x) args)
             | _ -> false) ins
         | Return (e, _) -> (match e with None -> true | Some e -> expression false e)
         | If (e, a, b, _) -> expression false e && block a && block b
         | Block b -> block b | _ -> false) b.bstmts in
  block body.sbody

let descriptor_setter_assignments env fn args =
  match fn, Hashtbl.find_opt local_function_bodies env#get_functionname with
  | Lval (Var (name, vid), NoOffset), Some body
       when Hashtbl.find_opt local_alias_enabled env#get_functionname = Some true ->
     (match local_setter_assignments body.sdecls name vid args with
      | Some (id, fields) when descriptor_address_is_confined body id -> Some fields
      | _ -> None)
  | _ -> None

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
                           && descriptor_address_is_confined f vi.vid))
        | _ -> false)
    | _ -> false in
  let assign lv source value = match type_of_lval f.sdecls lv with
    | Ok target ->
       (match fenv#get_type_unrolled target with TInt _ -> status_slot lv | _ -> true)
       && conversion target source value
    | _ -> false in
  let instruction_checked check_expr = function
          | Set (lv, e, _) ->
             clval lv && check_expr e && (match type_of_exp f.sdecls e with
                 | Ok source -> assign lv source (Some e) | _ -> false)
          | Call (lhs, fn, args, _) ->
             check_expr fn && List.for_all check_expr args && (match lhs with
               | None -> true
               | Some lv -> clval lv && (match type_of_exp f.sdecls fn with
                   | Ok typ -> (match fenv#get_type_unrolled typ with
                       | TFun (ret, _, _, _) -> assign lv ret None
                       | TPtr (TFun (ret, _, _, _), _) -> assign lv ret None
                       | _ -> false)
                   | _ -> false))
          | _ -> false in
  (* Numeric translation can treat C arithmetic as mathematical arithmetic.
     Restrict captured counts and their preceding guards to comparisons, slot
     copies and compile-time expressions with a checked representation. *)
  let rec count_expr e =
    match literal_value query e with
    | Some (XConst (IntConst _)) -> true
    | _ -> match e with
      | BinOp ((Lt | Le | Gt | Ge | Eq | Ne | LAnd | LOr | PlusPI | MinusPI | IndexPI), a, b, _) ->
         count_expr a && count_expr b
      | CastE (_, a) | UnOp (LNot, a, _) -> count_expr a
      | Lval lv | AddrOf lv | StartOf lv -> count_lval lv
      | Const _ | SizeOf _ | SizeOfE _ | AlignOf _ | AlignOfE _ -> true
      | _ -> false
  and count_lval (host, off) =
    (match host with Var _ -> true | Mem e -> count_expr e) && count_offset off
  and count_offset = function
    | NoOffset -> true
    | Field (_, rest) -> count_offset rest
    | Index (e, rest) -> count_expr e && count_offset rest in
  (* An unsupported conversion invalidates this path, not a sibling path that
     cannot reach the read. Return has no fallthrough. Join the safety of all
     continuing predecessors; never recover safety after a bad conversion.
     Keep alias/control-flow exclusions global. The contexts mirror the
     supported structured translation in cCHCfgTranslator. *)
  let checked_contexts check_expr check_lval =
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
             let lhs_ok = match ins with
               | Set (lv, _, _) | Call (Some lv, _, _, _) -> check_lval lv
               | _ -> true in
             let next = state = Some true && lhs_ok && instruction_checked check_expr ins in
             record (ctxt#add_instr i) next;
             (i + 1, if state = None then None else Some next)) (0, state) ins in
         snd result
      | Return (e, _) ->
         record ctxt#add_return
           (safe && (match e with Some e -> check_expr e | _ -> true));
         None
      | If (e, a, b, _) ->
         let next = safe && check_expr e in
         record ctxt#add_if_expr next;
         let incoming = if state = None then None else Some next in
         join (guarded_block ctxt#add_if_then incoming a)
           (guarded_block ctxt#add_if_else incoming b)
      | Block b -> guarded_block ctxt state b
      | _ -> Some false in
    ignore (guarded_block (CCHContext.mk_program_context ()) (Some true) f.sbody);
    contexts in
  let structured = block f.sbody in
  let certified = structured && aliases f.sbody
    && List.exists (function Attr ("codehawk_nested_scope_metadata_v1", []) -> true | _ -> false)
         f.sbody.battrs in
  Hashtbl.replace local_range_enabled env#get_functionname structured;
  Hashtbl.replace guarded_outputs_enabled env#get_functionname certified;
  Hashtbl.replace local_alias_enabled env#get_functionname certified;
  if certified then begin
    Hashtbl.replace guarded_output_contexts env#get_functionname (checked_contexts casts clval);
    Hashtbl.replace exact_count_contexts env#get_functionname
      (checked_contexts (fun e -> casts e && count_expr e) count_lval)
  end else begin
    Hashtbl.remove guarded_output_contexts env#get_functionname;
    Hashtbl.remove exact_count_contexts env#get_functionname
  end

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

let checked_context table env ctxt =
  guarded_output_initialization_enabled env
  && (match Hashtbl.find_opt table env#get_functionname with
      | Some contexts -> Hashtbl.find_opt contexts ctxt#get_cfg_context#index = Some true
      | _ -> false)
  && List.for_all (fun g -> g#get_value = None)
      CCHFileContract.file_contract#get_globalvar_contracts

let guarded_return_dependency (poq: po_query_int) ctxt callctxt callee op bound =
  if not (checked_context guarded_output_contexts poq#env ctxt) then None else
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

(* Reuse exact numeric field facts only while the descriptor's address is
   confined to modeled read-only getters and source-checked setters. *)
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
      | Ok vi when function_scope_local vi && descriptor_address_is_confined body vid ->
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
   Capacity belongs to the original malloc or guarded output call. *)
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
          | [Some (XConst (IntConst n))] when n#gt numerical_zero ->
             let query = object method fenv = env#get_fdecls end in
             (match call#get_arguments with
              | [arg] when (match literal_value query arg with
                      | Some (XConst (IntConst size)) -> size#equal n
                      | _ -> false) || checked_context exact_count_contexts env ctxt ->
                 Some (v, ConstantCapacity n)
              | _ -> None)
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

let memset_allocated_byte_range (env: c_environment_int) ctxt get_value args =
  let marker v name atts =
    [CCHCommand.make_c_cmd (CHLanguage.ASSIGN_SYM
         (allocated_byte_range_variable env (allocation_context env v),
          CHLanguage.SYM (new CHLanguage.symbol_t ~atts name)))] in
  match args with
  | [dest; _; len] ->
     (match resolve_allocated_region env get_value dest with
      | Some (v, capacity, first, None, None) when first#geq numerical_zero ->
         let query = object method fenv = env#get_fdecls end in
         let literal = literal_value query len in
         let exact = match literal with
           | Some _ -> literal
           | _ when checked_context exact_count_contexts env ctxt -> exact_local_length env get_value len
           | _ -> None in
         (match exact with
          | Some (XConst (IntConst count)) when count#gt numerical_zero ->
             (match capacity with
              | ConstantCapacity n when (first#add count)#gt n -> []
              | _ -> marker v "allocated-memset-bytes" [first#toString; count#toString])
          | _ ->
             let call = proof_scaffolding#get_direct_callsite env#get_functionname ctxt in
             if Option.is_none (unsigned_count_argument env call 3) then [] else
             marker v "allocated-memset-call"
               [first#toString; string_of_int (CCHContext.ccontexts#index_context ctxt)])
      | _ -> [])
  | _ -> []

type count_facts_t = {
    exact_count: (xpr_t * int list) option;
    count_lower: (numerical_t * int list) option;
    count_upper: (numerical_t * int list) option;
  }

let constant_count n = {
    exact_count = Some (XConst (IntConst n), []);
    count_lower = Some (n, []);
    count_upper = Some (n, []);
  }

let count_facts_at (poq: po_query_int) ctxt e =
  if not (checked_context exact_count_contexts poq#env ctxt) then None else
  match e with
  | Lval (Var (_, vid), NoOffset) ->
     (match poq#env#get_varinfo vid with
      | Error _ -> None
      | Ok vi ->
         let slot = poq#env#mk_program_var vi NoOffset CHLanguage.NUM_VAR_TYPE in
         let invariants = poq#get_context_invariants ctxt in
         let facts = List.filter (fun (inv: invariant_int) -> inv#applies_to_var slot) invariants in
         let exact_count = List.find_map (fun inv ->
             match inv#expr with
             | Some (XConst (IntConst _) as x) -> Some (x, [inv#index])
             | Some (XVar v as x) when not v#isTmp && poq#env#is_initial_parameter_value v ->
                let (param, offset) = poq#env#get_initial_parameter_vinfo v in
                if param.vparam > 0 && offset = NoOffset then Some (x, [inv#index]) else None
             | _ -> None) facts in
         let bound get better =
           let choose deps best inv =
             match get inv, best with
             | Some n, Some (previous, _) when not (better n previous) -> best
             | Some n, _ -> Some (n, inv#index :: deps)
             | _ -> best in
           let direct = List.fold_left (choose []) None facts in
           match exact_count with
           | Some (XConst (IntConst n), deps) -> Some (n, deps)
           | Some (XVar v, deps) ->
              List.fold_left (fun best (inv: invariant_int) ->
                  if inv#applies_to_var v then choose deps best inv else best) direct invariants
           | _ -> direct in
         Some {exact_count;
               count_lower = bound (fun inv -> inv#lower_bound) (fun a b -> a#gt b);
               count_upper = bound (fun inv -> inv#upper_bound) (fun a b -> a#lt b)})
  | _ -> None

let allocation_count_facts poq = function
  | ConstantCapacity n -> Some (constant_count n)
  | ArgumentCapacity (ctxt, e) -> count_facts_at poq ctxt e

(* Compare historical call arguments. Equality is usable only for constants or
   the same immutable entry value. Independent bounds remain useful when the
   caller clears a shorter prefix. A later assignment cannot enlarge either
   the captured allocation or the recorded clear. *)
let count_fits_capacity first count capacity =
  let same_value = function
    | XConst (IntConst a), XConst (IntConst b) -> a#equal b
    | XVar a, XVar b -> a#equal b
    | _ -> false in
  match first#equal numerical_zero, count.exact_count, capacity.exact_count with
  | true, Some (a, ad), Some (b, bd) when same_value (a, b) -> Some (ad @ bd)
  | _ ->
     (match count.count_upper, capacity.count_lower with
      | Some (count, cd), Some (capacity, bd) when (first#add count)#leq capacity -> Some (cd @ bd)
      | _ -> None)

let count_summary_dependencies (poq: po_query_int) =
  let current = poq#get_proof_obligation#get_context#get_cfg_context#index in
  List.concat_map (fun call ->
      if call#get_context#get_cfg_context#index = current then [] else
        let callee = call#get_callee in
        let predicates = match poq#get_summary callee.vname with
          | Some summary ->
             summary.fs_postconditions @ summary.fs_error_postconditions @ summary.fs_sideeffects
          | None -> call#get_postassumes in
        List.map (fun (predicate, _) -> PostAssumption (callee.vid, predicate)) predicates)
    poq#get_function_direct_callsites

let prove_allocated_bytes (poq: po_query_int) ctxt address requested =
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
       when first#geq numerical_zero ->
     let range = match span, leaf with
       | Some span, Some leaf ->
          (* A field is covered by clearing its containing object, but the
             requested read must still fit within the field itself. *)
          Option.map (fun deps -> constant_count span, deps)
            (count_fits_capacity numerical_zero requested (constant_count leaf))
       | _ -> Some (requested, []) in
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
          (match poq#get_function_return_value_buffer_size v, capacity with
           | Some (assumptions, XConst (IntConst n)), ConstantCapacity cap when n#equal cap ->
              let callee = poq#env#get_callvar_callee v in
              Some (origins, PostAssumption (callee.vid, XNewMemory ReturnValue) :: assumptions)
           | _ -> None) in
     let livevar = allocated_live_variable poq#env (allocation_context poq#env v) in
     let live = List.find_opt (fun (inv: invariant_int) -> match inv#get_fact with
         | NonRelationalFact (var, FInitializedSet syms) when var#equal livevar ->
            syms <> [] && List.for_all (fun s ->
                s#getBaseName = "allocated-live" && s#getAttributes = []) syms
         | _ -> false) facts in
     (match permission, live, allocation_count_facts poq capacity, range with
      | Some (origins, assumptions), Some live, Some capacity_facts, Some (width, leaf_deps) ->
         let variable = allocated_byte_range_variable poq#env (allocation_context poq#env v) in
         List.find_map (fun (inv: invariant_int) -> match inv#get_fact with
             | NonRelationalFact (var, FInitializedSet syms) when var#equal variable && syms <> [] ->
                let covers s =
                  let check start count =
                    if start#lt numerical_zero || first#lt start then None else
                    match count_fits_capacity (first#sub start) width count with
                    | Some deps ->
                       Option.map (fun bounds -> deps @ bounds)
                         (count_fits_capacity start count capacity_facts)
                    | None -> None in
                  try match s#getBaseName, s#getAttributes with
                  | "allocated-memset-bytes", [start; count] ->
                     check (mkNumericalFromString start) (constant_count (mkNumericalFromString count))
                  | "allocated-memset-call", [start; index] ->
                     let callctxt = CCHContext.ccontexts#get_context (int_of_string index) in
                     let call = proof_scaffolding#get_direct_callsite poq#fname callctxt in
                     Option.bind (unsigned_count_argument poq#env call 3) (fun e ->
                         Option.bind (count_facts_at poq callctxt e) (check (mkNumericalFromString start)))
                  | _ -> None
                  with Failure _ | Invalid_argument _ | CCHUtilities.CCHFailure _ -> None in
                let coverage = List.filter_map covers syms in
                if List.length coverage <> List.length syms then None else
                let bounds = leaf_deps @ List.concat coverage in
                let assumptions =
                  if bounds = [] then assumptions else assumptions @ count_summary_dependencies poq in
                Some (DEnvC (inv#index :: live#index :: (origins @ !aliases @ bounds), assumptions))
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

(* An entry initialization contract needs a frame up to its actual use. A
   whole-function frame also covers loops and gotos. The additional prefix
   certificate accepts only structured, acyclic control flow, joining every
   continuing predecessor and stopping paths at Return. It cannot omit a
   later opaque call that might reach the use through a backedge. *)
let preserves_entry_bytes (poq: po_query_int) target_context =
  let ordinary_local vid =
    match poq#env#get_varinfo vid with
    | Ok vi when vi.vparam = 0 && vi.vstorage <> Static
                 && stack_address_lifetime_known poq#env vi && not vi.vglob ->
       Some vi
    | _ -> None in
  let calls = proof_scaffolding#get_direct_callsites poq#fname in
  let instruction = function
    | Set ((Var (_, vid), off), _, _) ->
       (match ordinary_local vid with
        | Some vi -> CCHTypesSize.has_ordinary_layout fenv vi.vtype
                     && Option.is_some (contained_subobject poq vi.vtype off)
        | _ -> false)
    | Call (None, Lval (Var ("memcpy", vid), NoOffset), [dest; _; length], _)
         when not (fenv#is_application_function vid) && List.exists (fun call ->
             call#get_callee.vid = vid && call#get_header = "lib:string") calls ->
       (match addressed_local dest, literal_value poq length with
        | Some ((Var (_, id), off) as lv), Some (XConst (IntConst n))
             when n#geq numerical_zero ->
           (match ordinary_local id with
            | Some vi when CCHTypesSize.has_ordinary_layout fenv vi.vtype ->
               (match contained_subobject poq vi.vtype off, type_of_lval poq#fenv lv with
                | Some _, Ok typ ->
                   (match sizeof poq typ with Some width -> n#leq width | _ -> false)
                | _ -> false)
            | _ -> false)
        | _ -> false)
    | _ -> false in
  let rec block b = List.for_all (fun s -> match s.skind with
      | Instr instructions -> List.for_all instruction instructions
      | Return _ | Break _ | Continue _ | Goto _ -> true
      | If (_, yes, no, _) -> block yes && block no
      | Block inner | Loop (inner, _, _, _) | Switch (_, inner, _, _) -> block inner
      | _ -> false) b.bstmts in
  let rec acyclic_block b = List.for_all (fun s -> match s.skind with
      | Instr instructions -> List.for_all (function Set _ | Call _ -> true | _ -> false) instructions
      | Return _ | Break _ -> true
      | If (_, yes, no, _) -> acyclic_block yes && acyclic_block no
      | Switch (_, inner, _, _) -> acyclic_block inner
      | Block inner -> acyclic_block inner
      | _ -> false) b.bstmts in
  let prefix fn =
    let contexts = Hashtbl.create 17 in
    let record ctxt state =
      Hashtbl.replace contexts ctxt#get_cfg_context#index (state = Some true) in
    let join left right = match left, right with
      | None, state | state, None -> state
      | Some left, Some right -> Some (left && right) in
    let rec walk_block ctxt state b =
      List.fold_left (fun state stmt -> walk_stmt (ctxt#add_stmt stmt.sid) state stmt)
        state b.bstmts
    and walk_stmt ctxt state stmt = match stmt.skind with
      | Instr instructions ->
         snd (List.fold_left (fun (index, state) ins ->
             (* Call-entry requirements use the state before the instruction. *)
             record (ctxt#add_instr index) state;
             let next = match state with
               | None -> None
               | Some safe -> Some (safe && instruction ins) in
             index + 1, next) (0, state) instructions)
      | Return _ -> record ctxt#add_return state; None
      | If (_, yes, no, _) ->
         record ctxt#add_if_expr state;
         join (walk_block ctxt#add_if_then state yes)
           (walk_block ctxt#add_if_else state no)
      | Switch (_, inner, _, _) ->
         record ctxt#add_switch_expr state;
         (* A switch has only forward case entries and breaks, because the
          * syntax certificate excludes loops, gotos and assembly. Facts at
          * earlier instructions remain usable. Without modeling case entry
          * and fallthrough, no prefix certificate is issued in or after it. *)
         ignore (walk_block ctxt (Some false) inner);
         (match state with None -> None | Some _ -> Some false)
      | Block inner -> walk_block ctxt state inner
      | _ -> Some false in
    ignore (walk_block (CCHContext.mk_program_context ()) (Some true) fn.sbody);
    Hashtbl.find_opt contexts target_context#get_cfg_context#index = Some true in
  match Hashtbl.find_opt local_function_bodies poq#fname with
  | Some fn ->
     List.exists (function Attr ("codehawk_no_global_pragmas_v1", []) -> true | _ -> false)
       fn.sbody.battrs
     && (block fn.sbody
         || (List.exists (function Attr ("codehawk_nested_scope_metadata_v1", []) -> true | _ -> false)
               fn.sbody.battrs
             && acyclic_block fn.sbody && prefix fn))
  | _ -> false

let entry_index_upper (poq: po_query_int) ctxt e =
  match literal_value poq e with
  | Some (XConst (IntConst n)) when n#geq numerical_zero -> Some (n, [])
  | _ ->
     match e with
     | Lval (Var (_, vid), NoOffset) ->
        (match poq#env#get_varinfo vid with
         | Ok vi when vi.vparam > 0 && not vi.vaddrof && vi.vattr = [] ->
            (match fenv#get_type_unrolled vi.vtype with
             | TInt (kind, _) when CCHTypesSize.has_ordinary_layout fenv vi.vtype ->
                (* The frame forbids changing formals. Inspect the exact
                   entry value as well as its current program variable. *)
                let slot = poq#env#mk_program_var vi NoOffset CHLanguage.NUM_VAR_TYPE in
                let facts = poq#get_context_invariants ctxt in
                let bound (v, deps) =
                  List.find_map (fun (inv: invariant_int) ->
                      match inv#get_fact with
                      | NonRelationalFact (vv, FIntervalValue (low, Some high))
                           when vv#equal v && high#geq numerical_zero
                             && (match low with
                                 | Some n -> n#geq numerical_zero
                                 | _ -> is_unsigned_type kind) ->
                         Some (high, inv#index :: deps)
                      | _ -> None) facts in
                (match bound (slot, []) with
                 | Some _ as result -> result
                 | _ ->
                    List.find_map (fun (inv: invariant_int) ->
                        match inv#expr with
                        | Some (XVar v) when inv#applies_to_var slot
                                             && poq#env#is_initial_parameter_value v ->
                           let param, off = poq#env#get_initial_parameter_vinfo v in
                           if param.vid = vid && off = NoOffset
                           then bound (v, [inv#index]) else None
                        | _ -> None) facts)
             | _ -> None)
         | _ -> None)
     | _ -> None

let entry_field_offset typ key name =
  match fenv#get_type_unrolled typ with
  | TComp (k, _) when k = key && CCHTypesSize.has_ordinary_layout fenv typ ->
     let comp = fenv#get_comp key in
     List.find_map (fun field ->
         if field.fname = name then
           Option.map (fun n -> n, field.ftype)
             (constant (CCHTypesSize.ordinary_field_offset fenv field))
         else None) comp.cfields
  | _ -> None

let prove_entry_initialized_bytes (poq: po_query_int) ctxt address requested =
  let contracts = CCHFileContract.file_contract in
  if not (contracts#has_function_contract poq#fname) then None else
  let premises = (contracts#get_function_contract poq#fname)#get_preconditions in
  let rec field typ off =
    match off with
    | NoOffset -> Some numerical_zero
    | Field ((name, key), tail) ->
       Option.bind (entry_field_offset typ key name) (fun (offset, member) ->
           Option.map (fun n -> offset#add n) (field member tail))
    | _ -> None in
  let rec region = function
    | Lval (Var (_, vid), NoOffset) ->
       (match poq#env#get_varinfo vid with
        | Ok vi when vi.vparam > 0 && not vi.vaddrof && vi.vattr = []
                     && is_pointer_type (fenv#get_type_unrolled vi.vtype) ->
           Some (vi.vparam, numerical_zero, [])
        | _ -> None)
    | CastE (typ, e) when is_pointer_type (fenv#get_type_unrolled typ) ->
       (match type_of_exp poq#fenv e with
        | Ok source when is_pointer_type (fenv#get_type_unrolled source) -> region e
        | _ -> None)
    | BinOp ((PlusPI | IndexPI), base, index, _) ->
       (match region base, entry_index_upper poq ctxt index,
              get_pointer_expr_target_type poq#fenv base with
        | Some (parameter, start, deps), Some (upper, bounds), Ok elem
             when CCHTypesSize.has_ordinary_layout fenv elem ->
           (match sizeof poq elem with
            | Some stride when stride#gt numerical_zero ->
               Some (parameter, start#add (upper#mult stride), deps @ bounds)
            | _ -> None)
        | _ -> None)
    | AddrOf (Mem base, off) | StartOf (Mem base, off) ->
       (match region base, get_pointer_expr_target_type poq#fenv base with
        | Some (parameter, start, deps), Ok typ ->
           Option.map (fun offset -> parameter, start#add offset, deps) (field typ off)
        | _ -> None)
    | _ -> None in
  match requested with
  | Some bytes when bytes#gt numerical_zero ->
     (match region address with
      | Some (parameter, start, deps) ->
         List.find_map (function
             | XInitializedRange (ArgValue (ParFormal n, ArgNoOffset), NumConstant len) as p
                  when n = parameter && start#geq numerical_zero && (start#add bytes)#leq len ->
                (match CCHPOPredicate.xpredicate_to_po_predicate poq#fenv p with
                 | Ok pred when preserves_entry_bytes poq ctxt ->
                    Some (DEnvC (deps, [ApiAssumption pred]))
                 | _ -> None)
             | _ -> None) premises
      | _ -> None)
  | _ -> None

(* Infer only a required scalar/union parameter prefix, not table contents.
   The caller must establish it. Authored contracts are left unchanged, and a
   write/call before the read prevents using an entry requirement at that read. *)
let mandatory_entry_instruction (poq: po_query_int) target =
  let found = ref false in
  let rec block ctxt b = List.for_all (fun stmt ->
      let ctxt = ctxt#add_stmt stmt.sid in
      match stmt.skind with
      | Instr instructions ->
         List.iteri (fun index _ ->
             if (ctxt#add_instr index)#get_cfg_context#index = target#get_cfg_context#index
             then found := true) instructions;
         true
      | Block inner -> block ctxt inner
      | _ -> false) b.bstmts in
  match Hashtbl.find_opt local_function_bodies poq#fname with
  | Some fn -> ignore (block (CCHContext.mk_program_context ()) fn.sbody); !found
  | _ -> false

let parameter_initialized_requirement (poq: po_query_int) ctxt address length =
  if CCHFileContract.file_contract#has_function_contract poq#fname then None else
  let rec parameter = function
    | CastE (target, value) when is_pointer_type (fenv#get_type_unrolled target) ->
       (match type_of_exp poq#fenv value with
        | Ok source when is_pointer_type (fenv#get_type_unrolled source) -> parameter value
        | _ -> None)
    | Lval (Var (_, vid), NoOffset) ->
       (match poq#env#get_varinfo vid with
        | Ok vi when vi.vparam > 0 && not vi.vglob && not vi.vaddrof && vi.vattr = []
                     && not (is_volatile_type (fenv#get_type_unrolled vi.vtype)) ->
           (match fenv#get_type_unrolled vi.vtype with
            | TPtr (target, _) ->
               let target = fenv#get_type_unrolled target in
               let scalar = match target with
                 | TInt _ | TFloat _ -> true
                 | TComp (key, _) -> not (fenv#get_comp key).cstruct
                 | _ -> false in
               if scalar && not (range_type_volatile [] target)
                  && CCHTypesSize.has_ordinary_layout fenv target
               then Option.map (fun size -> vi, size) (sizeof poq target) else None
            | _ -> None)
        | _ -> None)
    | _ -> None in
  match parameter address, Option.bind (literal_value poq length) constant with
  | Some (vi, size), Some count when count#gt numerical_zero && count#leq size
       && count#leq (range_of_type poq#fenv (TInt (IInt, [])))#max
       && mandatory_entry_instruction poq ctxt
       && preserves_entry_bytes poq ctxt ->
     let predicate = PInitializedRange
         (Lval (Var (vi.vname, vi.vid), NoOffset), make_constant_exp count) in
     (match CCHPOPredicate.po_predicate_to_xpredicate poq#fenv predicate with
      | Ok (XInitializedRange (ArgValue (ParFormal _, ArgNoOffset), NumConstant _)) -> Some predicate
      | _ -> None)
  | _ -> None

let prove_initialized_range_facts poq ctxt address length =
  let entry = Option.bind (literal_value poq length) constant in
  match prove_entry_initialized_bytes poq ctxt address entry with
  | Some _ as proof -> proof
  | _ ->
  match addressed_source_at poq ctxt address,
        exact_local_length poq#env (context_local_value poq ctxt) length with
  | Some (lv, start), Some x ->
     (match constant x with
      | Some n -> initialized_local_bytes ~start poq ctxt lv n
      | _ -> None)
  | _ ->
     let requested = match literal_value poq length with
       | Some (XConst (IntConst n)) when n#gt numerical_zero -> Some (constant_count n)
       | _ when Option.is_some (unsigned_count_kind poq#env length) ->
          count_facts_at poq ctxt length
       | _ -> None in
     Option.bind requested (prove_allocated_bytes poq ctxt address)

let memcpy_call poq sequence =
  let origin = poq#env#get_byte_sequence_origin sequence in
  let callee = poq#env#get_callvar_callee origin in
  let ctxt = poq#env#get_callvar_context origin in
  if callee.vname = "memcpy"
     && proof_scaffolding#has_direct_callsite poq#fname ctxt then
    let call = proof_scaffolding#get_direct_callsite poq#fname ctxt in
    if call#get_header = "lib:string" then Some (origin, call) else None
  else None

(* An exact copy from caller storage or a shared field can reduce to an initialized-byte
   requirement at the copy. The alias is used to select this case, never as
   evidence of byte contents, bounds, or a live referent. *)
let reduce_caller_copy (poq: po_query_int) call source length n =
  let ctxt = call#get_context in
  let entry_parameter root =
    let root =
      if poq#env#is_memory_address root then
        match poq#env#get_memory_address root with
        | mem, NoOffset -> (match mem#get_base with CBaseVar (v, _) -> v | _ -> root)
        | _ -> root
      else root in
    poq#env#is_initial_parameter_value root
    && let param, offset = poq#env#get_initial_parameter_vinfo root in
       param.vparam > 0 && offset = NoOffset in
  let rec pointer_root = function
    | CastE (typ, e) when is_pointer_type (fenv#get_type_unrolled typ) ->
       pointer_root e
    | BinOp ((PlusPI | IndexPI), e, _, _) -> pointer_root e
    | Lval (Var (_, vid), NoOffset) ->
       (match poq#env#get_varinfo vid with
        | Ok vi when not vi.vglob && not vi.vaddrof && vi.vattr = []
                     && is_pointer_type (fenv#get_type_unrolled vi.vtype)
                     && not (is_volatile_type (fenv#get_type_unrolled vi.vtype)) ->
           let slot = poq#env#mk_program_var vi NoOffset CHLanguage.NUM_VAR_TYPE in
           List.exists (fun (inv: invariant_int) ->
               inv#applies_to_var slot
               && match inv#expr with
                  | Some (XVar root) -> entry_parameter root
                  | _ -> false) (poq#get_context_invariants ctxt)
        | _ -> false)
    | _ -> false in
  let rec field = function
    | CastE (typ, e) when is_pointer_type (fenv#get_type_unrolled typ) -> field e
    | AddrOf ((Mem base, Field _) as lv) when pointer_root base ->
       (match type_of_lval poq#fenv lv with
        | Ok typ -> (match sizeof poq typ with Some size -> n#leq size | _ -> false)
        | _ -> false)
    | _ -> false in
  (* A global descriptor selects a requirement at this call, not an entry
     premise or a stable table image. Later descriptor writes cannot change
     the point at which this local supporting obligation is checked. *)
  let rec global_pointer_root = function
    | CastE (typ, e) when is_pointer_type (fenv#get_type_unrolled typ) ->
       (match type_of_exp poq#fenv e with
        | Ok source when is_pointer_type (fenv#get_type_unrolled source) -> global_pointer_root e
        | _ -> false)
    | BinOp ((PlusPI | IndexPI), base, _, _) -> global_pointer_root base
    | (Lval (Var (_, vid), _) as e) ->
       (match poq#env#get_varinfo vid, type_of_exp poq#fenv e with
        | Ok vi, Ok typ when vi.vglob && vi.vattr = []
             && not (is_volatile_type (fenv#get_type_unrolled vi.vtype))
             && is_pointer_type (fenv#get_type_unrolled typ)
             && not (is_volatile_type (fenv#get_type_unrolled typ)) -> true
        | _ -> false)
    | _ -> false in
  let rec global_field = function
    | CastE (typ, e) when is_pointer_type (fenv#get_type_unrolled typ) ->
       (match type_of_exp poq#fenv e with
        | Ok source when is_pointer_type (fenv#get_type_unrolled source) -> global_field e
        | _ -> false)
    | AddrOf ((Mem base, Field _) as lv) when global_pointer_root base ->
       (match get_pointer_expr_target_type poq#fenv base, type_of_lval poq#fenv lv with
        | Ok parent, Ok typ when CCHTypesSize.has_ordinary_layout fenv parent
             && not (range_type_volatile [] parent) && not (range_type_volatile [] typ) ->
           (match sizeof poq typ with Some size -> n#leq size | _ -> false)
        | _ -> false)
    | _ -> false in
  let certified_global_field =
    match Hashtbl.find_opt local_function_bodies poq#fname with
    | Some fn ->
       List.exists (function Attr ("codehawk_no_global_pragmas_v1", []) -> true | _ -> false)
         fn.sbody.battrs && global_field source
    | _ -> false in
  let rec parameter_object = function
    | CastE (typ, e) when is_pointer_type (fenv#get_type_unrolled typ) ->
       parameter_object e
    | (Lval (Var _, NoOffset) as pointer) when pointer_root pointer ->
       (match get_pointer_expr_target_type poq#fenv pointer with
        | Ok typ when not (range_type_volatile [] typ) ->
           (match sizeof poq typ with Some size -> n#leq size | _ -> false)
        | _ -> false)
    | _ -> false in
  match literal_value poq length with
  | Some (XConst (IntConst width)) when n#gt numerical_zero && n#equal width
       && (field source || parameter_object source || certified_global_field) ->
     let predicate = PInitializedRange (source, length) in
     let location = call#get_location in
     poq#add_local_spo location ctxt predicate;
     Some (DReduced ([], [LocalAssumption predicate]),
           "memcpy destination read requires " ^ n#toString
           ^ " initialized source bytes at copy on line " ^ string_of_int location.line)
  | _ -> None

(* Carry a copied automatic object's prefix to a later call entry. The CFG
   joins all predecessors; a dirty fallthrough cannot borrow a sibling case's
   copy. This deliberately excludes loops, gotos, assembly and nested locals.
   Source bytes remain a requirement at the original copy, not an image axiom. *)
let prove_copied_local_range (poq: po_query_int) target address length =
  let target_index = target#get_cfg_context#index in
  let calls = proof_scaffolding#get_direct_callsites poq#fname in
  let standard_copy ctxt vid = List.find_opt (fun call ->
      call#get_context#get_cfg_context#index = ctxt#get_cfg_context#index
      && call#get_callee.vid = vid && call#get_callee.vname = "memcpy"
      && call#get_header = "lib:string" && not (fenv#is_application_function vid)) calls in
  match addressed_local address, Option.bind (literal_value poq length) constant,
        Hashtbl.find_opt local_function_bodies poq#fname with
  | Some (Var (_, vid), NoOffset), Some requested, Some fn when requested#gt numerical_zero ->
     (match poq#env#get_varinfo vid with
      | Ok vi when vi.vparam = 0 && not vi.vglob && vi.vstorage <> Static && vi.vattr = []
           && stack_address_lifetime_known poq#env vi
           && not (range_type_volatile [] vi.vtype)
           && CCHTypesSize.has_ordinary_layout fenv vi.vtype ->
         let flags = fn.sbody.battrs in
         let certified name = List.exists (function Attr (n, []) -> n = name | _ -> false) flags in
         if not (certified "codehawk_no_global_pragmas_v1"
                 && certified "codehawk_nested_scope_metadata_v1") then None else
         let rec mentions_address = function
           | AddrOf (Var (_, id), _) | StartOf (Var (_, id), _) when id = vid -> true
           | AddrOf lv | StartOf lv | Lval lv -> mentions_lval lv
           | CastE (_, e) | UnOp (_, e, _) | SizeOfE e | AlignOfE e -> mentions_address e
           | BinOp (_, a, b, _) -> mentions_address a || mentions_address b
           | Const _ | SizeOf _ | AlignOf _ -> false
           | _ -> true
         and mentions_lval (host, off) =
           (match host with Var _ -> false | Mem e -> mentions_address e) || mentions_offset off
         and mentions_offset = function
           | NoOffset -> false
           | Field (_, rest) -> mentions_offset rest
           | Index (e, rest) -> mentions_address e || mentions_offset rest in
         let nodes = Hashtbl.create 31 in
         let rec collect ctxt block = List.for_all (fun stmt ->
             let ctxt = ctxt#add_stmt stmt.sid in
             Hashtbl.replace nodes stmt.sid (ctxt, stmt);
             match stmt.skind with
             | Instr instructions -> List.for_all (fun (index, instruction) ->
                 let point = ctxt#add_instr index in
                 match instruction with
                 | Set (lv, e, _) -> not (mentions_lval lv || mentions_address e)
                 | Call (lhs, callee, args, _) ->
                    not (mentions_address callee)
                    && (match lhs with None -> true | Some lv -> not (mentions_lval lv))
                    && (not (List.exists mentions_address args)
                        || point#get_cfg_context#index = target_index
                        || (match lhs, callee with
                            | None, Lval (Var (_, id), NoOffset) -> Option.is_some (standard_copy point id)
                            | _ -> false))
                 | VarDecl _ -> true
                 | _ -> false) (List.mapi (fun i ins -> i, ins) instructions)
             | If (e, yes, no, _) -> not (mentions_address e)
                 && collect ctxt#add_if_then yes && collect ctxt#add_if_else no
             | Switch (e, body, _, _) -> not (mentions_address e) && collect ctxt body
             | Block body -> collect ctxt body
             | Return (e, _) -> (match e with None -> true | Some e -> not (mentions_address e))
             | Break _ -> true
             | _ -> false) block.bstmts in
         if not (collect (CCHContext.mk_program_context ()) fn.sbody) then None else
         let sorted = List.sort_uniq compare in
         let consistent = Hashtbl.fold (fun id (_, stmt) ok -> ok
             && List.for_all (fun next -> match Hashtbl.find_opt nodes next with
                 | Some (_, successor) -> List.mem id successor.preds | _ -> false) stmt.succs
             && List.for_all (fun previous -> match Hashtbl.find_opt nodes previous with
                 | Some (_, predecessor) -> List.mem id predecessor.succs | _ -> false) stmt.preds
             && sorted stmt.succs = List.sort compare stmt.succs
             && sorted stmt.preds = List.sort compare stmt.preds) nodes true in
         if not consistent then None else
         let same left right = match left, right with
           | None, None -> true
           | Some a, Some b -> a#get_context#get_cfg_context#index = b#get_context#get_cfg_context#index
           | _ -> false in
         let join left right = if same left right then left else None in
         let incoming = Hashtbl.create 31 and queue = Queue.create () in
         let found = ref None in
         let propagate id value = match Hashtbl.find_opt incoming id with
           | None -> Hashtbl.add incoming id value; Queue.add id queue
           | Some old -> let next = join old value in
              if not (same old next) then begin Hashtbl.replace incoming id next; Queue.add id queue end in
         let transfer ctxt state = function
           | Set ((Var (_, id), _), _, _) when id <> vid -> state
           | VarDecl (local, _) when local.vid <> vid -> state
           | Call (None, Lval (Var (_, id), NoOffset), [dest; _; count], _) ->
              (match standard_copy ctxt id, addressed_local dest,
                     Option.bind (literal_value poq count) constant with
               | Some call, Some (Var (_, target_vid), NoOffset), Some bytes when target_vid = vid ->
                  (match sizeof poq vi.vtype with
                   | Some size when bytes#geq requested && bytes#leq size -> Some call
                   | _ -> None)
               | Some _, Some (Var (_, other), _), _ when other <> vid -> state
               | _ -> None)
           | _ -> None in
         (match fn.sbody.bstmts with first :: _ -> propagate first.sid None | _ -> ());
         while not (Queue.is_empty queue) do
           let id = Queue.take queue in
           let ctxt, stmt = Hashtbl.find nodes id in
           let state = Hashtbl.find incoming id in
           let after = match stmt.skind with
             | Instr instructions -> snd (List.fold_left (fun (index, state) ins ->
                 let point = ctxt#add_instr index in
                 if point#get_cfg_context#index = target_index then found := state;
                 index + 1, transfer point state ins) (0, state) instructions)
             | _ -> state in
           List.iter (fun next -> propagate next after) stmt.succs
         done;
         Option.bind !found (fun call -> match call#get_arguments with
             | [_; source; count] ->
                Option.bind (Option.bind (literal_value poq count) constant) (fun bytes ->
                    Option.map fst (reduce_caller_copy poq call source count bytes))
             | _ -> None)
      | _ -> None)
  | _ -> None

(* A later case can recover the byte width selected by an earlier switch only
   when its controlling expression is unchanged. Use the actual CFG, including
   first-switch fallthrough, and reject a queried case with another predecessor.
   No global image facts or initialized source memory are introduced. *)
let prove_correlated_union_range (poq: po_query_int) target address length =
  let point_index ctxt = ctxt#get_cfg_context#index in
  let target_index = point_index target in
  let calls = proof_scaffolding#get_direct_callsites poq#fname in
  let standard_copy ctxt id = List.exists (fun call ->
      point_index call#get_context = point_index ctxt && call#get_callee.vid = id
      && call#get_callee.vname = "memcpy" && call#get_header = "lib:string"
      && not (fenv#is_application_function id)) calls in
  match addressed_local address, Option.bind (literal_value poq length) constant,
        Hashtbl.find_opt local_function_bodies poq#fname with
  | Some (Var (_, vid), NoOffset), Some requested, Some fn when requested#gt numerical_zero ->
     (match poq#env#get_varinfo vid with
      | Ok vi when vi.vparam = 0 && not vi.vglob && vi.vstorage <> Static && vi.vattr = []
           && stack_address_lifetime_known poq#env vi
           && not (range_type_volatile [] vi.vtype)
           && CCHTypesSize.has_ordinary_layout fenv vi.vtype ->
         let union_key = match fenv#get_type_unrolled vi.vtype with
           | TComp (key, _) when not (fenv#get_comp key).cstruct -> Some key | _ -> None in
         let certified name = List.exists (function Attr (n, []) -> n = name | _ -> false) fn.sbody.battrs in
         if union_key = None || not (certified "codehawk_no_global_pragmas_v1"
             && certified "codehawk_no_implicit_local_effects_v1"
             && certified "codehawk_nested_scope_metadata_v1") then None else
         let nodes = Hashtbl.create 31 and query = ref None in
         let rec collect ctxt block = List.for_all (fun stmt ->
             let ctxt = ctxt#add_stmt stmt.sid in
             if Hashtbl.mem nodes stmt.sid then false else begin
             Hashtbl.add nodes stmt.sid (ctxt, stmt);
             let labels_ok = List.for_all (function
                 | Case (e, _) -> Option.is_some (Option.bind (literal_value poq e) constant)
                 | CaseRange _ -> false | _ -> true) stmt.labels in
             labels_ok && match stmt.skind with
             | Instr instructions -> List.for_all (fun (i, ins) ->
                 if point_index (ctxt#add_instr i) = target_index then
                   query := (if i = 0 then Some stmt else None);
                 match ins with Set _ | Call _ | VarDecl _ -> true | _ -> false)
                 (List.mapi (fun i ins -> i, ins) instructions)
             | If (_, yes, no, _) -> collect ctxt#add_if_then yes && collect ctxt#add_if_else no
             | Switch (_, body, _, _) | Block body -> collect ctxt body
             | Return _ | Break _ -> true
             | _ -> false end) block.bstmts in
         if not (collect (CCHContext.mk_program_context ()) fn.sbody) then None else
         let unique xs = List.sort_uniq compare xs = List.sort compare xs in
         let consistent = Hashtbl.fold (fun id (_, stmt) ok -> ok
             && unique stmt.preds && unique stmt.succs
             && List.for_all (fun next -> match Hashtbl.find_opt nodes next with
                 | Some (_, s) -> List.mem id s.preds | _ -> false) stmt.succs
             && List.for_all (fun prev -> match Hashtbl.find_opt nodes prev with
                 | Some (_, s) -> List.mem id s.succs | _ -> false) stmt.preds) nodes true in
         if not consistent then None else
         (match !query with
          | Some q when List.length q.preds = 1 ->
             let _, parent = Hashtbl.find nodes (List.hd q.preds) in
             (match parent.skind with
              | Switch (selector, _, cases, _) when List.mem q.sid cases ->
                 let values = List.filter_map (function
                     | Case (e, _) -> Option.bind (literal_value poq e) constant | _ -> None) q.labels in
                 let only_cases = List.for_all (function Case _ -> true | _ -> false) q.labels in
                 let refs = ref [] in
                 let ordinary typ = not (range_type_volatile [] typ)
                     && CCHTypesSize.has_ordinary_layout fenv typ in
                 let rec stable_expression e =
                   (match type_of_exp poq#fenv e with Ok typ -> ordinary typ | _ -> false)
                   && match e with
                   | Const (CInt _) -> true
                   | Lval lv -> stable_lvalue lv
                   | CastE (typ, e) ->
                      (match type_of_exp poq#fenv e with
                       | Ok source ->
                          (is_pointer_type (fenv#get_type_unrolled typ)
                           = is_pointer_type (fenv#get_type_unrolled source)) && stable_expression e
                       | _ -> false)
                   | BinOp ((PlusPI | IndexPI | PlusA | MinusA), a, b, _) ->
                      stable_expression a && stable_expression b
                   | _ -> false
                 and stable_lvalue (host, off) =
                   (match host with
                    | Var (_, id) -> refs := id :: !refs;
                       (match poq#env#get_varinfo id with
                        | Ok info -> info.vattr = [] && ordinary info.vtype | _ -> false)
                    | Mem e -> stable_expression e
                       && (match get_pointer_expr_target_type poq#fenv e with Ok typ -> ordinary typ | _ -> false))
                   && stable_offset off
                 and stable_offset = function
                   | NoOffset -> true | Field (_, rest) -> stable_offset rest
                   | Index (e, rest) -> stable_expression e && stable_offset rest in
                 let selector_kind = match type_of_exp poq#fenv selector with
                   | Ok typ -> (match fenv#get_type_unrolled typ with TInt _ -> Some typ | _ -> None)
                   | _ -> None in
                 if values = [] || not only_cases || selector_kind = None
                    || not (stable_expression selector) then None else
                 let selector_range = range_of_type poq#fenv (Option.get selector_kind) in
                 if not (List.for_all (fun n -> n#geq selector_range#min && n#leq selector_range#max) values)
                 then None else
                 let rec mentions id = function
                   | AddrOf (Var (_, other), _) | StartOf (Var (_, other), _) when id = other -> true
                   | AddrOf lv | StartOf lv | Lval lv -> mentions_lv id lv
                   | CastE (_, e) | UnOp (_, e, _) | SizeOfE e | AlignOfE e -> mentions id e
                   | BinOp (_, a, b, _) -> mentions id a || mentions id b
                   | Const _ | SizeOf _ | AlignOf _ -> false
                   | _ -> true
                 and mentions_lv id (host, off) =
                   (match host with Var _ -> false | Mem e -> mentions id e) || mentions_off id off
                 and mentions_off id = function
                   | NoOffset -> false | Field (_, rest) -> mentions_off id rest
                   | Index (e, rest) -> mentions id e || mentions_off id rest in
                 let nonescaping id = Hashtbl.fold (fun _ (ctxt, stmt) ok -> ok && match stmt.skind with
                     | Instr ins -> List.for_all (fun (i, ins) -> match ins with
                         | Set (lv, e, _) -> not (mentions_lv id lv || mentions id e)
                         | Call (lhs, callee, args, _) ->
                            not (mentions id callee)
                            && (match lhs with None -> true | Some lv -> not (mentions_lv id lv))
                            && (not (List.exists (mentions id) args)
                                || point_index (ctxt#add_instr i) = target_index
                                || (match lhs, callee with
                                    | None, Lval (Var (_, fnid), NoOffset) -> standard_copy (ctxt#add_instr i) fnid
                                    | _ -> false))
                         | VarDecl _ -> true | _ -> false) (List.mapi (fun i ins -> i, ins) ins)
                     | If (e, _, _, _) | Switch (e, _, _, _) -> not (mentions id e)
                     | Return (Some e, _) -> not (mentions id e)
                     | _ -> true) nodes true in
                 let private_local id = match poq#env#get_varinfo id with
                   | Ok info -> info.vparam = 0 && not info.vglob && info.vstorage <> Static
                       && info.vattr = [] && stack_address_lifetime_known poq#env info
                       && ordinary info.vtype && nonescaping id
                   | _ -> false in
                 if not (private_local vid) then None else
                 let reaching = Hashtbl.create 31 in
                 let rec backwards id = if not (Hashtbl.mem reaching id) then begin
                     Hashtbl.add reaching id ();
                     List.iter backwards (snd (Hashtbl.find nodes id)).preds end in
                 backwards q.sid;
                 let preserves_selector ctxt = function
                   | Set ((Var (_, id), off), _, _) -> not (List.mem id !refs)
                       && private_local id
                       && (match poq#env#get_varinfo id with
                           | Ok info -> Option.is_some (contained_subobject poq info.vtype off) | _ -> false)
                   | VarDecl (info, _) -> not (List.mem info.vid !refs)
                   | Call (None, Lval (Var (_, id), NoOffset), [dest; _; count], _) when standard_copy ctxt id ->
                      (match addressed_local dest, Option.bind (literal_value poq count) constant with
                       | Some ((Var (_, local), NoOffset) as lv), Some bytes
                            when not (List.mem local !refs) && private_local local ->
                          (match type_of_lval poq#fenv lv with
                           | Ok typ -> (match sizeof poq typ with Some size ->
                               bytes#geq numerical_zero && bytes#leq size | _ -> false)
                           | _ -> false)
                       | _ -> false)
                   | _ -> false in
                 let frame = Hashtbl.fold (fun id (ctxt, stmt) ok -> ok &&
                     (not (Hashtbl.mem reaching id) || id = q.sid || match stmt.skind with
                      | Instr ins -> List.for_all (fun (i, ins) -> preserves_selector (ctxt#add_instr i) ins)
                          (List.mapi (fun i ins -> i, ins) ins)
                      | _ -> true)) nodes true in
                 if not frame then None else
                 let establishes = function
                   | Set ((Var (_, id), Field ((field, key), NoOffset)), source, _) when id = vid && Some key = union_key ->
                      let field = List.find_opt (fun f -> f.fname = field) (fenv#get_comp key).cfields in
                      (match field with
                       | Some field when field.fbitfield = None && ordinary field.ftype ->
                          (match fenv#get_type_unrolled field.ftype, sizeof poq field.ftype with
                           | TInt (kind, _), Some size when size#geq requested ->
                              (match source with
                               | Lval (Var (_, input), NoOffset) ->
                                  (match poq#env#get_varinfo input with
                                   | Ok info when info.vparam > 0 && info.vattr = [] && ordinary info.vtype ->
                                      (match fenv#get_type_unrolled info.vtype with TInt (ik, _) -> ik = kind | _ -> false)
                                   | _ -> false)
                               | _ -> (match Option.bind (literal_value poq source) constant with
                                   | Some n -> let range = range_of_type poq#fenv field.ftype in
                                      n#geq range#min && n#leq range#max | _ -> false))
                           | _ -> false)
                       | _ -> false)
                   | _ -> false in
                 let check_value value =
                   let incoming = Hashtbl.create 31 and queue = Queue.create () in
                   let found = ref None and valid = ref true in
                   let propagate id state = match Hashtbl.find_opt incoming id with
                     | None -> Hashtbl.add incoming id state; Queue.add id queue
                     | Some old when old && not state -> Hashtbl.replace incoming id false; Queue.add id queue
                     | _ -> () in
                   (match fn.sbody.bstmts with first :: _ -> propagate first.sid false | _ -> ());
                   while not (Queue.is_empty queue) do
                     let id = Queue.take queue in
                     let _, stmt = Hashtbl.find nodes id in
                     let state = Hashtbl.find incoming id in
                     if id = q.sid then found := Some state;
                     let after = match stmt.skind with
                       | Instr ins -> List.fold_left (fun state ins ->
                           if establishes ins then true else match ins with
                           | Set ((Var (_, other), _), _, _) when other <> vid -> state
                           | VarDecl (info, _) when info.vid <> vid -> state
                           | Call (None, _, [dest; _; _], _) ->
                              (match addressed_local dest with Some (Var (_, other), _) when other <> vid -> state | _ -> false)
                           | _ -> false) state ins
                       | _ -> state in
                     let successors = match stmt.skind with
                       | Switch (e, _, cases, _) when exp_compare e selector = 0 ->
                          let case_nodes = List.filter_map (fun sid ->
                              Option.map snd (Hashtbl.find_opt nodes sid)) cases in
                          if List.length case_nodes <> List.length cases then valid := false;
                          (* Case labels undergo conversion to the promoted
                             selector type. Reject non-value-preserving cases
                             rather than comparing their unconverted integers. *)
                          if not (List.for_all (fun s -> List.for_all (function
                              | Case (label, _) ->
                                 (match Option.bind (literal_value poq label) constant with
                                  | Some n -> n#geq selector_range#min && n#leq selector_range#max
                                  | _ -> false)
                              | _ -> true) s.labels) case_nodes) then valid := false;
                          let matched = List.filter (fun s -> List.exists (function Case (e, _) ->
                              (match Option.bind (literal_value poq e) constant with Some n -> n#equal value | _ -> false)
                              | _ -> false) s.labels) case_nodes in
                          let selected = if matched <> [] then matched else List.filter (fun s ->
                              List.exists (function Default _ -> true | _ -> false) s.labels) case_nodes in
                          (match List.sort_uniq compare (List.map (fun s -> s.sid) selected) with
                           | [next] when List.mem next stmt.succs -> [next]
                           | _ -> valid := false; [])
                       | _ -> stmt.succs in
                     List.iter (fun next -> if Hashtbl.mem reaching next then propagate next after) successors
                   done;
                   !valid && !found = Some true in
                 if List.for_all check_value values then Some (DLocal []) else None
              | _ -> None)
          | _ -> None)
      | _ -> None)
  | _ -> None

let prove_initialized_range poq ctxt address length =
  match prove_initialized_range_facts poq ctxt address length with
  | Some _ as proof -> proof
  | _ -> match prove_copied_local_range poq ctxt address length with
     | Some _ as proof -> proof
     | _ -> prove_correlated_union_range poq ctxt address length

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
                        | _ when n#gt numerical_zero ->
                           (match prove_allocated_bytes poq call#get_context source (constant_count n) with
                            | Some _ as proof -> proof
                            | _ -> prove_entry_initialized_bytes poq call#get_context source (Some n))
                        | _ -> None in
                      match source_bytes with
                      | Some deps -> Some (deps,
                          "memcpy source bytes initialized at call; copied "
                          ^ n#toString ^ " bytes cover destination read")
                      | _ ->
                         (match Option.bind (literal_value poq length) constant with
                          | Some captured when captured#equal n ->
                             (match parameter_initialized_requirement poq call#get_context source length with
                              | Some predicate -> Some (DEnvC ([], [ApiAssumption predicate]),
                                  "memcpy requires initialized parameter bytes at entry, preserved to the copy")
                              | _ ->
                                 (match sizeof poq dtyp with
                                  | Some size when n#leq size -> reduce_caller_copy poq call source length n
                                  | _ -> None))
                          | _ ->
                             (match sizeof poq dtyp with
                              | Some size when n#leq size -> reduce_caller_copy poq call source length n
                              | _ -> None)))
                  | _ -> None)
              | _ -> None)
          | _ -> None)
      | _ -> None)
  | _ -> None
