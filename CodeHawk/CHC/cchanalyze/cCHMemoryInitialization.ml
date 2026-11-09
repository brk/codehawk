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
open CCHTypesCompare
open CCHTypesUtil
open CCHPreTypes
open CCHProofObligation
open CCHProofScaffolding
open CCHAnalysisTypes

let fenv = CCHFileEnvironment.file_environment

let constant = function XConst (IntConst n) -> Some n | _ -> None

let sizeof (poq: po_query_int) typ = constant (size_of_type poq#fenv typ)

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

let local_byte_range_variable (env: c_environment_int) vi =
  env#mk_augmentation_variable "$initialized-bytes$" "local-byte-range"
    vi.vid CHLanguage.SYM_VAR_TYPE

let local_byte_range_variables (env: c_environment_int) =
  List.map (local_byte_range_variable env) env#get_fdecls#get_locals

let register_local_byte_ranges (env: c_environment_int) (f: fundec) =
  let rec block b = List.for_all stmt b.bstmts
  and stmt s = match s.skind with
    | Instr ins -> List.for_all (function Set _ | Call _ -> true | _ -> false) ins
    | Return _ -> true
    | If (_, a, b, _) -> block a && block b
    | Block b -> block b
    | _ -> false in
  Hashtbl.replace local_range_enabled env#get_functionname (block f.sbody)

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

let memset_local_byte_range (env: c_environment_int) args =
  let query = object method fenv = env#get_fdecls end in
  let rec address = function
    | CastE (typ, e) when is_pointer_type typ -> address e
    | BinOp (PlusPI, e, index, _) ->
       (match address e, literal_value query index,
              get_pointer_expr_target_type env#get_fdecls e with
        | Some (lv, first), Some (XConst (IntConst i)), Ok typ
             when i#geq numerical_zero ->
           (match constant (size_of_type env#get_fdecls typ) with
            | Some n when n#gt numerical_zero -> Some (lv, first#add (i#mult n))
            | _ -> None)
        | _ -> None)
    | e -> Option.map (fun lv -> lv, numerical_zero) (addressed_local e) in
  if Hashtbl.find_opt local_range_enabled env#get_functionname <> Some true then [] else
  match args with
  | [dest; _; len] ->
     (match address dest, literal_value query len with
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
                   List.map (fun p -> PostAssumption (callee.vid, p))
                     (contracts#get_function_contract callee.vname)#get_sideeffects
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

let prove_initialized_range poq ctxt address length =
  match addressed_source poq address, literal_value poq length with
  | Some (lv, start), Some x ->
     (match constant x with
      | Some n -> initialized_local_bytes ~start poq ctxt lv n
      | _ -> None)
  | _ -> None

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
         (match addressed_local dest, addressed_source poq source, len, read with
          | Some ((Var (_, dvid), doff) as dlv), Some (slv, sstart), Some n,
            (Var (_, rvid), roff) when dvid = rvid ->
             (match local_type poq dlv, local_type poq read,
                    offset_suffix doff roff with
              | Some dtyp, Some ((TInt _ | TFloat ((FFloat | FDouble), _)) as rtyp),
                Some tail ->
                 (match relative_bytes poq dtyp tail, sizeof poq rtyp with
                  | Some start, Some width when (start#add width)#leq n ->
                     (match initialized_local_bytes ~start:sstart poq call#get_context slv n with
                      | Some deps -> Some (deps,
                          "memcpy source bytes initialized at call; copied "
                          ^ n#toString ^ " bytes cover destination read")
                      | _ -> None)
                  | _ -> None)
              | _ -> None)
          | _ -> None)
      | _ -> None)
  | _ -> None
