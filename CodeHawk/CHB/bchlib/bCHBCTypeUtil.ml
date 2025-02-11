(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2025 Aarno Labs LLC

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

(* chlib *)
open CHConstants
open CHLanguage
open CHPretty

(* chutil *)
open CHLogger
open CHTraceResult
open CHTimingLog

(* bchlib *)
open BCHBasicTypes
open BCHBCFiles
open BCHBCTypePretty
open BCHBCTypes


let string_printer = CHPrettyUtil.string_printer
let p2s = string_printer#print

(* Teach Printexc how to print our own exceptions *)
let () =
  Printexc.register_printer
    (function
      | BCH_failure e -> Some (p2s(e))
      | _ -> None (* for other exceptions *)
    )

(* ====================================================== common scalar types *)

let t_unknown = TUnknown []
let t_void = TVoid []
let t_vararg = TVarArg []

let t_bool = TInt (IBool, [])
let t_char = TInt (IChar, [])
let t_uchar = TInt (IUChar, [])
let t_wchar = TInt (IWChar, [])

let t_short = TInt (IShort, [])
let t_ushort = TInt (IUShort, [])
let t_int = TInt (IInt, [])
let t_uint = TInt (IUInt, [])
let t_long = TInt (ILong, [])
let t_ulong = TInt (IULong, [])

let t_float = TFloat (FFloat, FScalar, [])
let t_double = TFloat (FDouble, FScalar, [])
let t_longdouble = TFloat (FLongDouble, FScalar, [])

let t_voidptr = TPtr (TVoid [], [])
let t_refto t = TRef (t,[])
let t_ptrto t = TPtr (t,[])

let ptr_deref (t: btype_t): btype_t =
  match t with
  | TPtr (dty, _) -> dty
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [STR "Type is not a pointer type"]))

let t_charptr = t_ptrto t_char

let t_array (t: btype_t) (len: int) =
  TArray (t, Some (Const (CInt ((Int64.of_int len), IInt, None))), [])

let t_unknown_int = TUnknown [(Attr ("int", []))]

let t_unknown_int_size (size: int) = TUnknown [(Attr ("int-size", [AInt size]))]

let t_unknown_float = TUnknown [(Attr ("float", []))]


let t_named name = TNamed (name, [])


(* =========================================================== complex types *)

let to_tname s = SimpleName s


let t_comp ?(name_space=[]) name =
  TCppComp (to_tname name, List.map to_tname name_space, [])


let t_enum ?(name_space=[]) name =
  TCppEnum (to_tname name, List.map to_tname name_space, [])


let t_class ?(name_space=[]) name =
  BCHBCTypes.TClass (to_tname name, List.map to_tname name_space, [])


let t_tcomp ?(name_space=[]) name = TCppComp (name, name_space, [])


let t_tenum ?(name_space=[]) name = TCppEnum (name, name_space, [])


let t_tclass ?(name_space=[]) name =
  BCHBCTypes.TClass (name, name_space, [])


let t_function ?(is_varargs=false) (returntype:btype_t) (args:bfunarg_t list) =
  TFun (returntype, Some args, is_varargs, [])


let t_fsignature
      ?(is_varargs=false) (returntype: btype_t) (args: (string * btype_t) list) =
  let funargs = List.map (fun (name, ty) -> (name, ty, [])) args in
  t_function ~is_varargs returntype funargs


let t_vararg_function (returntype:btype_t) (args:bfunarg_t list) =
  TFun (returntype, Some args, true, [])


let t_function_anon (returntype:btype_t) =
  TFun (returntype, None, false, [])

(* =========================================================== string -> type *)

let convert_string_to_type (name: string): btype_t traceresult =
  match name with
  | "char" -> Ok (TInt (IChar, []))
  | "signed char" -> Ok (TInt (ISChar, []))
  | "unsigned char" -> Ok (TInt (IUChar, []))
  | "wchar_t" -> Ok (TInt (IWChar, []))
  | "bool" -> Ok (TInt (IBool, []))
  | "int" -> Ok (TInt (IInt, []))
  | "unsigned int" -> Ok (TInt (IUInt, []))
  | "short" -> Ok (TInt (IShort, []))
  | "unsigned short" -> Ok (TInt (IUShort, []))
  | "long" -> Ok (TInt (ILong, []))
  | "unsigned long" -> Ok (TInt (IULong, []))
  | "long long" -> Ok (TInt (ILongLong, []))
  | "unsigned long long" -> Ok (TInt (IULongLong, []))
  | "int8_t" -> Ok (TInt (ISChar, []))
  | "uint8_t" -> Ok (TInt (IUChar, []))
  | "int16_t" -> Ok (TInt (IShort, []))
  | "uint16_t" -> Ok (TInt (IUShort, []))
  | "int32_t" -> Ok (TInt (IInt, []))
  | "uint32_t" -> Ok (TInt (IUInt, []))
  | "int64_t" -> Ok (TInt (ILongLong, []))
  | "uint64_t" -> Ok (TInt (IULongLong, []))
  | "int128_t" -> Ok (TInt (IInt128, []))
  | "uint128_t" -> Ok (TInt (IUInt128, []))
  | "float" -> Ok (TFloat (FFloat, FScalar, []))
  | "double" -> Ok (TFloat (FDouble, FScalar, []))
  | "long double" -> Ok (TFloat (FLongDouble, FScalar, []))
  | "complex" -> Ok (TFloat (FComplexFloat, FScalar, []))
  | "double complex" -> Ok (TFloat (FComplexDouble, FScalar, []))
  | "long double complex" -> Ok (TFloat (FComplexLongDouble, FScalar, []))
  | "void" -> Ok (TVoid [])
  | _ ->
     if bcfiles#has_typedef name then
       Ok (bcfiles#get_typedef name)
     else
       Error [
           __FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
         ^ "unable to convert type name " ^ name]

(* =============================================================== attributes *)

let get_attributes (t: btype_t): b_attributes_t =
  match t with
  | TVoid attrs
    | TInt (_, attrs)
    | TFloat (_, _, attrs)
    | TPtr (_, attrs)
    | TRef (_, attrs)
    | THandle (_, attrs)
    | TArray (_, _, attrs)
    | TFun (_, _, _, attrs)
    | TNamed (_, attrs)
    | TComp (_, attrs)
    | TEnum (_, attrs)
    | TCppComp (_, _, attrs)
    | TCppEnum (_, _, attrs)
    | TClass (_, _, attrs)
    | TBuiltin_va_list attrs
    | TVarArg attrs
    | TUnknown attrs -> attrs


(* ========================================================== type predicates *)

let is_void t = match t with TVoid _ -> true | _ -> false

let is_int t = match t with TInt _ -> true | _ -> false

let is_enum t = match t with TEnum _ -> true | _ -> false

let is_float t = match t with TFloat _ -> true | _ -> false

let is_float_float t = match t with TFloat (FFloat, _, _) -> true | _ -> false

let is_float_double t = match t with TFloat (FDouble, _, _) -> true | _ -> false

let is_pointer t = match t with TPtr _ -> true | _ -> false

let is_void_pointer t = match t with TPtr (TVoid _, _) -> true | _ -> false

let is_scalar t = (is_int t) || (is_float t) || (is_pointer t)

let is_pointer_to_struct t = match t with TPtr (TComp _,_) -> true | _ -> false

let is_struct_type t = match t with TComp _ -> true | _ -> false

let is_array_type t = match t with TArray _ -> true | _ -> false

let is_function_type t =
  match t with TFun _ | TPtr (TFun _,_) -> true | _ -> false

let is_unknown_type t =
  match t with
  | TUnknown _ -> true
  | TNamed ("unknown", _) -> true
  | _ -> false

let is_known_type t = match t with TUnknown _ -> false | _ -> true

let is_unsigned t = match t with
  | TInt (ik,_) ->
    begin
      match ik with
      |  IUChar | IUInt | IUShort | IULong | IULongLong -> true
      | _ -> false
    end
  | _ -> false

let is_volatile t =
  match get_attributes t with
  | [] -> false
  | attrs ->
     List.exists (fun attr ->
         match attr with
         | Attr ("volatile", _) -> true
         | _ -> false) attrs


let is_stdcall (t: btype_t) =
  match t with
  | TFun (_, _, _, attrs)
    | TPtr (TFun (_, _, _, _), attrs) ->
     List.exists (fun a ->
         match a with
         | Attr ("stdcall", _) -> true
         | _ -> false) attrs
  | _ -> false


let get_element_type (t: btype_t) =
  match t with
  | TArray (eltty, _, _) -> eltty
  | _ ->
     raise (BCH_failure (LBLOCK [STR "Not an array type"]))


let get_array_length (t: btype_t): int traceresult =
  match t with
  | TArray (_, Some len, _) ->
     (match len with
      | Const (CInt (i64, _, _)) -> Ok (Int64.to_int i64)
      | _ ->
         Error ["Array does not have a constant length: " ^ (exp_to_string len)])
  | TArray _ ->
     Error ["Array does not have a length"]
  | _ ->
     Error ["get_array_length: not an array: " ^ (btype_to_string t)]


(* ======================================================= size and alignment *)

let resolve_type (btype: btype_t) = bcfiles#resolve_type btype


let size_of_int_ikind (k: ikind_t) =
  match k with
  | IChar | ISChar | IUChar -> 1
  | IWChar -> 2
  | IBool -> 1
  | IInt | IUInt -> 4
  | IShort | IUShort -> 2
  | ILong | IULong -> 4
  | ILongLong | IULongLong -> 8
  | IInt128 | IUInt128 -> 16
  | INonStandard (_, s) -> s


let size_to_int_ikind ?(signed=true) (size:int) =
  match size with
  | 1 -> if signed then ISChar else IUChar
  | 2 -> if signed then IShort else IUShort
  | 4 -> if signed then IInt else IUInt
  | 8 -> if signed then ILongLong else IULongLong
  | _ -> INonStandard (signed,size)


let align_of_int_ikind (k: ikind_t): int =
  match k with
  | IChar | ISChar | IUChar -> 1
  | IWChar -> 2
  | IBool -> 1
  | IInt | IUInt -> 4
  | IShort | IUShort -> 2
  | ILong | IULong -> 4
  | ILongLong | IULongLong -> 8
  | IInt128 | IUInt128 -> 16
  | INonStandard (_, s) -> s


let size_of_float_fkind (k: fkind_t) =
  match k with
  | FFloat -> 4
  | FDouble -> 8
  | FLongDouble -> 16
  | FComplexFloat -> 8
  | FComplexDouble -> 16
  | FComplexLongDouble -> 32


let align_of_float_fkind (k: fkind_t): int =
  match k with
  | FFloat -> 4
  | FDouble -> 8
  | FLongDouble -> 16
  | FComplexFloat -> 8
  | FComplexDouble -> 16
  | FComplexLongDouble -> 32


type offset_accumulator_t = {
    oa_first_free: int;         (* the first free byte *)
    oa_last_field_start: int;   (* byte where the last field started *)
    oa_last_field_width: int    (* width of the previous field without padding *)
  }


let start_oa = {
    oa_first_free = 0;
    oa_last_field_start = 0;
    oa_last_field_width = 0
  }


let _oa_to_pretty (oa: offset_accumulator_t) =
  LBLOCK [
      STR "oa_ff: ";
      INT oa.oa_first_free;
      STR "; oa_lfs: ";
      INT oa.oa_last_field_start;
      STR "; oa_lfw: ";
      INT oa.oa_last_field_width]


let add_trailing (numBytes: int) (roundto: int): int =
  (numBytes + roundto - 1) land (lnot (roundto - 1))


let rec align_of_btype (t: btype_t): int traceresult =
  match t with
  | TInt (k, _) -> Ok (align_of_int_ikind k)
  | TEnum (name, _) when bcfiles#has_enuminfo name ->
     align_of_btype (TInt ((bcfiles#get_enuminfo name).bekind, []))
  | TEnum (name, _) ->
     let _ = chlog#add "unknown enum" (LBLOCK [STR "align: "; STR name]) in
     align_of_btype (TInt (IUInt, []))
  | TFloat (fk, _, _) -> Ok (align_of_float_fkind fk)
  | TNamed (_name, _) ->
     tbind
       ~msg:"align_of_btype"
       align_of_btype
       (bcfiles#resolve_type t)
  | TComp (ckey, _) when bcfiles#has_compinfo ckey ->
     alignof_comp (bcfiles#get_compinfo ckey)
  | TComp (ckey, _) ->
     begin
       log_error
         "Struct key without definition: %d [%s:%d]"
         ckey
         __FILE__ __LINE__;
       chlog#add "unknown compinfo" (LBLOCK [STR "align: "; INT ckey]);
       Error ["Struct key without definition " ^ (btype_to_string t)]
     end
  | TArray (tt, _, _) -> align_of_btype tt
  | TPtr _
    | TRef _
    | THandle _
    | TCppComp _
    | TCppEnum _
    | TClass _
    | TBuiltin_va_list _
    | TVarArg _
    | TUnknown _ -> Ok 4   (* all systems are 32-bit for now *)
  | TVoid _ -> Error ["Unable to determine alignment for void"]
  | TFun _ ->
     Error ["Unable to determine alignment of function: "
            ^ (btype_to_string t)]


and alignof_comp (comp: bcompinfo_t): int traceresult =
  let aligns = List.map (fun finfo -> align_of_btype finfo.bftype) comp.bcfields in
  tfold_list_fail (fun mx a -> if a > mx then a else mx) (Ok 0) aligns


and size_of_btype (t: btype_t): int traceresult =
  match t with
  | TInt (ik, _) -> Ok (size_of_int_ikind ik)
  | TFloat (fk, _, _) -> Ok (size_of_float_fkind fk)
  | TEnum (name, _) when bcfiles#has_enuminfo name ->
     size_of_btype (TInt ((bcfiles#get_enuminfo name).bekind, []))
  | TEnum (name, _) ->
     begin
       log_error
         "Unable to resolve enum info for %s (assuming unsigned int) [%s:%d]"
         name
         __FILE__ __LINE__;
       chlog#add "unknown enum" (LBLOCK [STR "size: "; STR name]);
       size_of_btype (TInt (IUInt, []))
     end
  | TArray (tt, Some len, _) -> size_of_btype_array tt len
  | TArray (_, _, _) ->
     Error ["Unable to determine size of array without length: "
            ^ (btype_to_string t)]
  | TComp (ckey, _) when bcfiles#has_compinfo ckey ->
     size_of_btype_comp (bcfiles#get_compinfo ckey)
  | TComp (ckey, _) ->
     begin
       log_error
         "Struct key without definition: %d [%s:%d]"
         ckey
         __FILE__ __LINE__;
       chlog#add "unknown compinfo" (LBLOCK [STR "size: "; INT ckey]);
       Error ["Struct key without definition: " ^ (btype_to_string t)]
     end
  | TNamed (name, _) ->
     tbind
       ~msg:("size_of_btype: " ^ name)
       size_of_btype
       (bcfiles#resolve_type t)
       (*
     let t_r = bcfiles#resolve_type t in
     (match t_r with
      | Ok v -> size_of_btype v
      | Error e ->
         begin
           log_error
             "type resolution problem (default type size: 4): %s [%s:%d]"
             (String.concat "; " e)
             __FILE__ __LINE__;
           4
         end) *)
  | TPtr _
    | TVoid _
    | TRef _
    | THandle _
    | TCppComp _
    | TCppEnum _
    | TClass _
    | TBuiltin_va_list _
    | TVarArg _
    | TUnknown _ -> Ok 4   (* all systems are 32-bit for now *)
  (* | TVoid _ -> raise (BCH_failure (LBLOCK [STR "Type size error: tvoid"])) *)
  | TFun _ ->
     Error ["unable to get size of function type: " ^ (btype_to_string t)]


and size_of_btype_array (t: btype_t) (len: bexp_t): int traceresult =
  let rec getlen (e: bexp_t): int traceresult =
    match e with
    | Const (CInt (i64, _, _)) -> Ok (Int64.to_int i64)
    | BinOp (PlusA, e1, e2, _) ->
       tmap2
         (fun v1 v2 -> v1 + v2)
         (getlen e1)
         (getlen e2)
    | BinOp (MinusA, e1, e2, _) ->
       tmap2
         (fun v1 v2 -> v1 - v2)
         (getlen e1)
         (getlen e2)
    | SizeOf t -> size_of_btype t
    | _ ->
       Error ["Unable to evaluate array size expressing: " ^ (exp_to_string e)] in

  let arraylen = getlen len in
  let elementsize = size_of_btype t in
  let elementsize =
    tmap2 (fun s a -> add_trailing s a) elementsize (align_of_btype t) in
  tmap2 (fun v1 v2 -> v1 * v2) arraylen elementsize


and size_of_btype_comp (comp: bcompinfo_t): int traceresult =
  if comp.bcstruct then
    let lastoff =
      List.fold_left (fun acc_r finfo ->
          tbind (fun acc -> offset_of_field_acc ~finfo ~acc) acc_r)
        (Ok start_oa) comp.bcfields in
    let size =
      tmap2 (fun o a -> add_trailing o.oa_first_free a)
        lastoff (align_of_btype (TComp (comp.bckey, []))) in
    size
  else    (* union *)
    let fieldsizes =
      List.map (fun finfo -> size_of_btype finfo.bftype) comp.bcfields in
    let size =
      tfold_list_fail (fun mx a -> if a > mx then a else mx) (Ok 0) fieldsizes in
    size


and offset_of_field_acc
~(finfo: bfieldinfo_t)
~(acc: offset_accumulator_t): offset_accumulator_t traceresult =
  let ftype = bcfiles#resolve_type finfo.bftype in
  let falign = tbind align_of_btype ftype in
  let fsize = tbind size_of_btype ftype in
  let newstart =
    tmap2 (fun o a -> add_trailing o a) (Ok acc.oa_first_free) falign in
  tmap2
    (fun newstart fsize ->
      {oa_first_free = newstart + fsize;
       oa_last_field_start = newstart;
       oa_last_field_width = fsize
    })
    newstart
    fsize

(* =============================================================== comparison *)

let list_compare = CHUtil.list_compare


let attribute_compare a1 a2 =
  match (a1, a2) with (Attr (s1, _), Attr (s2, _)) -> Stdlib.compare s1 s2


let attributes_compare l1 l2 = list_compare l1 l2 attribute_compare


let rec typ_compare t1 t2 =
  match (t1,t2) with
  | (TUnknown attrs1,TUnknown attrs2) -> attributes_compare attrs1 attrs2
  | (TUnknown _,_) -> -1
  | (_, TUnknown _) -> 1
  | (TVoid attrs1,TVoid attrs2) -> attributes_compare attrs1 attrs2
  | (TVoid _,_) -> -1
  | (_, TVoid _) -> 1
  | (TInt (i1,attrs1), TInt (i2,attrs2)) ->
     let l0 = Stdlib.compare i1 i2 in
     if l0 = 0 then attributes_compare attrs1 attrs2 else l0
  | (TInt _, _) -> -1
  | (_, TInt _) -> 1
  | (TFloat (f1,r1,attrs1), TFloat (f2,r2,attrs2)) ->
    let l0 = Stdlib.compare f1 f2 in
    if l0 = 0 then
      let l1 = Stdlib.compare r1 r2 in
      if l1 = 0 then
	attributes_compare attrs1 attrs2
      else l1
    else l0
  | (TFloat _, _) -> -1
  | (_, TFloat _) -> 1
  | (TPtr (tt1,attrs1), TPtr (tt2,attrs2)) ->
    let l0 = typ_compare tt1 tt2 in
    if l0 = 0 then attributes_compare attrs1 attrs2 else l0
  | (TPtr _, _) -> -1
  | (_, TPtr _) -> 1
  | (TRef (tt1,attrs1), TRef (tt2,attrs2)) ->
    let l0 = typ_compare tt1 tt2 in
    if l0 = 0 then attributes_compare attrs1 attrs2 else l0
  | (TRef _,_) -> -1
  | (_, TRef _) -> 1
  | (THandle (s1,attrs1),THandle (s2,attrs2)) ->
    let l0 = Stdlib.compare s1 s2 in
    if l0 = 0 then attributes_compare attrs1 attrs2 else l0
  | (THandle _,_) -> -1
  | (_, THandle _) -> 1
  | (TArray (tt1,x1,attrs1), TArray (tt2,x2,attrs2)) ->
    let l0 = typ_compare tt1 tt2 in
    if l0 = 0 then
      let l1 = opt_exp_compare x1 x2 in
      if l1 = 0 then
	attributes_compare attrs1 attrs2
      else l1
    else l0
  | (TArray _, _) -> -1
  | (_, TArray _) -> 1
  | (TFun (tt1,args1,_,attrs1), TFun (tt2,args2,_,attrs2)) ->
    let l0 = typ_compare tt1 tt2 in
    if l0 = 0 then
      let l1 = opt_arg_list_compare args1 args2 in
      if l1 = 0 then
	attributes_compare attrs1 attrs2
      else l1
    else l0
  | (TFun _, _) -> -1
  | (_, TFun _) -> 1
  | (TNamed (n1,attrs1), TNamed (n2,attrs2)) ->
    let l0 = Stdlib.compare n1 n2 in
    if l0 = 0 then attributes_compare attrs1 attrs2 else l0
  | (TNamed _,_) -> -1
  | (_, TNamed _) -> 1
  | (TComp (ckey1, attrs1), TComp (ckey2, attrs2)) ->
    let l0 = Stdlib.compare ckey1 ckey2 in
    if l0 = 0 then attributes_compare attrs1 attrs2 else l0
  | (TComp _, _) -> -1
  | (_, TComp _) -> 1
  | (TEnum (ename1, attrs1), TEnum (ename2, attrs2)) ->
    let l0 = Stdlib.compare ename1 ename2 in
    if l0 = 0 then attributes_compare attrs1 attrs2 else l0
  | (TEnum _, _) -> -1
  | (_, TEnum _) -> 1
  | (TClass (n1, ns1, attrs1), TClass (n2, ns2, attrs2)) ->
    let l0 = tname_compare n1 n2 in
    if l0 = 0 then
      let l1 = list_compare ns1 ns2 tname_compare in
      if l1 = 0 then attributes_compare attrs1 attrs2 else l1
    else l0
  | (TClass _, _) -> -1
  | (_, TClass _) -> 1
  | (TCppComp (n1, ns1, attrs1), TCppComp (n2, ns2, attrs2)) ->
    let l0 = tname_compare n1 n2 in
    if l0 = 0 then
      let l1 = list_compare ns1 ns2 tname_compare in
      if l1 = 0 then attributes_compare attrs1 attrs2 else l1
    else l0
  | (TCppComp _, _) -> -1
  | (_, TCppComp _) -> 1
  | (TCppEnum (n1, ns1, attrs1), TCppEnum (n2, ns2, attrs2)) ->
    let l0 = tname_compare n1 n2 in
    if l0 = 0 then
      let l1 = list_compare ns1 ns2 tname_compare in
      if l1 = 0 then attributes_compare attrs1 attrs2 else l1
    else l0
  | (TCppEnum _, _) -> -1
  | (_, TCppEnum _) -> 1
  | (TBuiltin_va_list a1, TBuiltin_va_list a2) -> attributes_compare a1 a2
  | (TBuiltin_va_list _, _) -> -1
  | (_, TBuiltin_va_list _) -> 1
  | (TVarArg attrs1, TVarArg attrs2) -> attributes_compare attrs1 attrs2


and tname_compare t1 t2 =
  match (t1,t2) with
  | (SimpleName n1, SimpleName n2) -> Stdlib.compare n1 n2
  | (SimpleName _,_) -> -1
  | (_, SimpleName _) -> 1
  | (TemplatedName (b1,args1), TemplatedName (b2,args2)) ->
    let l0 = tname_compare b1 b2 in
    if l0 = 0 then list_compare args1 args2 typ_compare else l0


and opt_arg_list_compare (a1: bfunarg_t list option) (a2: bfunarg_t list option) =
  match (a1, a2) with
  | (Some l1, Some l2) ->
     list_compare l1 l2 (fun (_, t1, _) (_, t2, _) -> typ_compare t1 t2)
  | (Some _, _) -> -1
  | (_, Some _) -> 1
  | _ -> 0


and opt_exp_compare (e1: bexp_t option) (e2: bexp_t option) =
  CHUtil.optvalue_compare e1 e2 exp_compare


and exp_compare e1 e2 =
  match (e1,e2) with
  | (Const c1, Const c2) -> constant_compare c1 c2
  | (Const _, _) -> -1
  | (_, Const _) -> 1
  | (Lval l1, Lval l2) -> lval_compare l1 l2
  | (Lval _, _) -> -1
  | (_, Lval _) -> 1
  | (SizeOf t1, SizeOf t2) -> typ_compare t1 t2
  | (SizeOf _, _) -> -1
  | (_, SizeOf _) -> 1
  | (Real e1, Real e2) -> exp_compare e1 e2
  | (Real _, _) -> -1
  | (_, Real _) -> 1
  | (Imag e1, Imag e2) -> exp_compare e1 e2
  | (Imag _, _) -> -1
  | (_, Imag _) -> 1
  | (SizeOfE e1, SizeOfE e2) -> exp_compare e1 e2
  | (SizeOfE _, _) -> -1
  | (_, SizeOfE _) -> 1
  | (SizeOfStr s1, SizeOfStr s2) -> Stdlib.compare s1 s2
  | (SizeOfStr _, _) -> -1
  | (_, SizeOfStr _) -> 1
  | (AlignOf t1, AlignOf t2) -> typ_compare t1 t2
  | (AlignOf _, _) -> -1
  | (_, AlignOf _) -> 1
  | (AlignOfE e1, AlignOfE e2) -> exp_compare e1 e2
  | (AlignOfE _, _) -> -1
  | (_, AlignOfE _) -> 1
  | (UnOp (op1, e1, t1), UnOp (op2, e2, t2)) ->
     let l0 = Stdlib.compare op1 op2 in
     if l0 = 0 then
       let l1 = exp_compare e1 e2 in
       if l1 = 0 then
         typ_compare t1 t2
       else
         l1
     else
       l0
  | (UnOp _, _) -> -1
  | (_, UnOp _) -> 1
  | (BinOp (op1, e11, e21, t1), BinOp (op2, e12, e22, t2)) ->
     let l0 = Stdlib.compare op1 op2 in
     if l0 = 0 then
       let l1 = exp_compare e11 e12 in
       if l1 = 0 then
         let l2 = exp_compare e21 e22 in
         if l2 = 0 then
           typ_compare t1 t2
         else
           l2
       else
         l1
     else
       l0
  | (BinOp _, _) -> -1
  | (_, BinOp _) -> 1
  | (Question (e11, e21, e31, t1), Question (e12, e22, e32, t2)) ->
     let l0 = exp_compare e11 e12 in
     if l0 = 0 then
       let l1 = exp_compare e21 e22 in
       if l1 = 0 then
         let l2 = exp_compare e31 e32 in
         if l2 = 0 then
           typ_compare t1 t2
         else
           l2
       else
         l1
     else
       l0
  | (Question _, _) -> -1
  | (_, Question _) -> 1
  | (CastE (t1, e1), CastE (t2, e2)) ->
     let l0 = typ_compare t1 t2 in
     if l0 = 0 then
       exp_compare e1 e2
     else
       l0
  | (CastE _, _) -> -1
  | (_, CastE _) -> 1
  | (AddrOf l1, AddrOf l2) -> lval_compare l1 l2
  | (AddrOf _, _) -> -1
  | (_, AddrOf _) -> 1
  | (AddrOfLabel l1, AddrOfLabel l2) -> Stdlib.compare l1 l2
  | (AddrOfLabel _, _) -> -1
  | (_, AddrOfLabel _) -> 1
  | (StartOf l1, StartOf l2) -> lval_compare l1 l2
  | (StartOf _, _) -> -1
  | (_, StartOf _) -> 1
  | (FnApp (_, e1, e1l), FnApp (_, e2, e2l)) ->
     let l0 = exp_compare e1 e2 in
     if l0 = 0 then
       opt_exp_list_compare e1l e2l
     else
       l0
  | (FnApp _, _) -> -1
  | (_, FnApp _) -> 1
  | (CnApp (s1, e1l, t1), CnApp (s2, e2l, t2)) ->
     let l0 = Stdlib.compare s1 s2 in
     if l0 = 0 then
       let l1 = opt_exp_list_compare e1l e2l in
       if l1 = 0 then
         typ_compare t1 t2
       else
         l1
     else
       l0


and opt_exp_list_compare (l1: (bexp_t option) list) (l2: (bexp_t option) list) =
  list_compare l1 l2 opt_exp_compare


and lval_compare (lv1: blval_t) (lv2: blval_t) =
  match (lv1, lv2) with
  | ((h1, o1), (h2, o2)) ->
     let l0 = lhost_compare h1 h2 in
     if l0 = 0 then
       offset_compare o1 o2
     else
       l0


and lhost_compare (h1: blhost_t) (h2: blhost_t) =
  match (h1, h2) with
  | (Var v1, Var v2) -> Stdlib.compare v1 v2
  | (Var _, _) -> -1
  | (_, Var _) -> 1
  | (Mem e1, Mem e2) -> exp_compare e1 e2


and offset_compare (o1: boffset_t) (o2: boffset_t) =
  match (o1, o2) with
  | (NoOffset, NoOffset) -> 0
  | (NoOffset, _) -> -1
  | (_, NoOffset) -> 1
  | (Field (f1, oo1), Field (f2, oo2)) ->
     let l0 = Stdlib.compare f1 f2 in
     if l0 = 0 then
       offset_compare oo1 oo2
     else
       l0
  | (Field _, _) -> -1
  | (_, Field _) -> 1
  | (Index (e1, oo1), Index (e2, oo2)) ->
     let l0 = exp_compare e1 e2 in
     if l0 = 0 then
       offset_compare oo1 oo2
     else
       l0


and constant_compare c1 c2 =
  match (c1,c2) with
  | (CInt (i1,k1,_), CInt (i2,k2,_)) ->
    let l0 = Int64.compare i1 i2 in if l0 = 0 then Stdlib.compare k1 k2 else l0
  | (CInt _, _) -> -1
  | (_, CInt _) -> 1
  | (CStr s1, CStr s2) -> Stdlib.compare s1 s2
  | (CStr _, _) -> -1
  | (_, CStr _) -> 1
  | (CWStr l1, CWStr l2) ->  list_compare l1 l2 Int64.compare
  | (CWStr _, _) -> -1
  | (_, CWStr _) -> 1
  | (CChr c1, CChr c2) -> Char.compare c1 c2
  | (CChr _, _) -> -1
  | (_, CChr _) -> 1
  | (CReal (f1,_,_), CReal (f2,_,_)) -> Stdlib.compare f1 f2
  | (CReal _, _) -> -1
  | (_, CReal _) -> 1
  | (CEnum (e1,iname1,ename1), CEnum (e2,iname2,ename2)) ->
    let l0 = Stdlib.compare iname1 iname2 in
    if l0 = 0 then
      let l1 = Stdlib.compare ename1 ename2 in
      if l1 = 0 then
	exp_compare e1 e2
      else l1
    else l0


let btype_compare = typ_compare

let btype_equal (t1: btype_t) (t2: btype_t) = (btype_compare t1 t2) = 0

let bexp_compare = exp_compare


(* ============================================================== abstraction *)

let btype_abstract (btype: btype_t): symbol_t =
  let aux (t: btype_t) (_acc: string) =
    match t with
    | TUnknown [] -> "t_unknown"
    | TUnknown [Attr ("int", [])] -> "t_int"
    | TUnknown [Attr ("int-size", [AInt n])] -> "t_int_" ^ (string_of_int n)
    | TUnknown [Attr ("float", [])] -> "t_float"
    | TInt (IInt, []) -> "t_int_32s"
    | TInt (IUInt, []) -> "t_int_32u"
    | TInt (IShort, []) -> "t_int_16s"
    | TInt (IUShort, []) -> "t_int_16u"
    | TInt (IChar, []) -> "t_int_8s"
    | TInt (IUChar, []) -> "t_int_8u"
    | TFloat (FFloat, FScalar, []) -> "t_float_32"
    | TFloat (FDouble, FScalar, []) -> "t_float_64"
    | TFloat (FLongDouble, FScalar, []) -> "t_float_128"
    | TPtr (TVoid [], []) -> "t_ptr"
    | _ -> "t_unknown" in
  new symbol_t (aux btype "")


let btype_concretize (abtype: symbol_t): btype_t =
  let aux (s: string) (_acc: btype_t option) =
    match s with
    | "t_unknown" -> TUnknown []
    | "t_int" -> TUnknown [Attr ("int", [])]
    | "t_float" -> TUnknown [Attr ("float", [])]
    | "t_int_8" -> TUnknown [Attr ("int-size", [AInt 8])]
    | "t_int_16" -> TUnknown [Attr ("int-size", [AInt 16])]
    | "t_int_32" -> TUnknown [Attr ("int-size", [AInt 32])]
    | "t_int_8s" -> TInt (IChar, [])
    | "t_int_8u" -> TInt (IUChar, [])
    | "t_int_16s" -> TInt (IShort, [])
    | "t_int_16u" -> TInt (IUShort, [])
    | "t_int_32s" -> TInt (IInt, [])
    | "t_int_32u" -> TInt (IUInt, [])
    | "t_ptr" -> TPtr (TVoid [], [])
    | _ -> TUnknown [] in
  aux abtype#getBaseName None


let btype_join (btypes: btype_t list): btype_t =
  let abtypes = List.map btype_abstract btypes in
  match abtypes with
  | [] -> TUnknown []
  | [ty] -> btype_concretize ty
  | hdty::tl ->
     let joinabty =
       List.fold_left (fun acc ty ->
           match acc with
           | None -> None
           | Some accty -> ordered_sym_join accty ty) (Some hdty) tl in
     (match joinabty with
      | None -> TUnknown []
      | Some abty -> btype_concretize abty)


let btype_meet (btypes: btype_t list): btype_t option =
  let abtypes = List.map btype_abstract btypes in
  match abtypes with
  | [] -> None
  | [ty] -> Some (btype_concretize ty)
  | hdty :: tl ->
     let meetabty =
       List.fold_left (fun acc ty ->
           match acc with
           | None -> None
           | Some accty ->
              if ordered_sym_leq accty ty then
                acc
              else if ordered_sym_leq ty accty then
                Some ty
              else
                None) (Some hdty) tl in
     (match meetabty with
      | Some abty -> Some (btype_concretize abty)
      | _ -> None)


(* ================================================================ promotion *)

let promote_float (ty: btype_t): btype_t =
  match ty with
  | TFloat (FFloat, rep, attrs) -> TFloat (FDouble, rep, attrs)
  | TFloat _ -> ty
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [STR "Not a float: "; btype_to_pretty ty]))


let promote_int (ty: btype_t): btype_t =
  match ty with
  | TInt ((IChar | ISChar | IWChar | IBool | IShort), attrs) ->
     TInt (IInt, attrs)
  | TInt ((IUChar | IUShort), attrs) -> TInt (IUInt, attrs)
  | TInt _ -> ty
  | _ ->
     raise
       (BCH_failure
          (LBLOCK[STR "Not an int: "; btype_to_pretty ty]))

(* ============================================================= field layout *)

let has_field_layout (comp: bcompinfo_t): bool =
  List.for_all
    (fun f -> match f.bfieldlayout with Some _ -> true | _ -> false)
    comp.bcfields


let layout_fields (comp: bcompinfo_t): bcompinfo_t =
  if has_field_layout comp then
    comp
  else
    if comp.bcstruct then
      let (acc_r, newfields) =
        List.fold_left (fun (acc_r, fields) finfo ->
            match acc_r with
            | Error e -> (Error e, [])
            | Ok acc ->
               let fieldoffset_r = offset_of_field_acc ~finfo ~acc in
               let fieldlayout_r =
                 tmap
                   (fun fieldoffset ->
                     Some (fieldoffset.oa_last_field_start,
                           fieldoffset.oa_last_field_width))
                   fieldoffset_r in
               match fieldoffset_r, fieldlayout_r with
               | Ok fieldoffset, Ok fieldlayout ->
                  (Ok fieldoffset,
                   {finfo with bfieldlayout = fieldlayout} :: fields)
               | Error e, _
                 | _, Error e -> (Error e, [])) ((Ok start_oa), []) comp.bcfields in
      match acc_r with
      | Ok _ -> {comp with bcfields = List.rev newfields}
      | Error e ->
         begin
           log_error
             "Unable to layout fields for struct %s: %s [%s:%d]"
             comp.bcname
             (String.concat ", " e)
             __FILE__ __LINE__;
           comp
         end
    else   (* union *)
      let newfields_r =
        List.fold_left (fun acc_r finfo ->
            match acc_r with
            | Error e -> Error e
            | Ok acc ->
               let fieldlayout_r =
                 tmap (fun s -> Some (0, s)) (size_of_btype finfo.bftype) in
               match fieldlayout_r with
               | Ok fieldlayout ->
                  Ok (({finfo with bfieldlayout = fieldlayout}) :: acc)
               | Error e -> Error e)
          (Ok []) comp.bcfields in
      match newfields_r with
      | Ok newfields -> {comp with bcfields = newfields}
      | Error e ->
         begin
           log_error
             "Unable to layout fields for union %s: %s [%s:%d]"
             comp.bcname
             (String.concat "; " e)
             __FILE__ __LINE__;
           comp
         end


let get_struct_field_name (bfinfo: bfieldinfo_t): string = bfinfo.bfname

let get_struct_field_type (bfinfo: bfieldinfo_t): btype_t = bfinfo.bftype

let get_struct_field_layout (bfinfo: bfieldinfo_t): fieldlayout_t option =
  bfinfo.bfieldlayout


let get_struct_field_offset (bfinfo: bfieldinfo_t): int option =
  match get_struct_field_layout bfinfo with
  | Some (offset, _) -> Some offset
  | _ -> None


let get_struct_field_size (bfinfo: bfieldinfo_t): int option =
  match get_struct_field_layout bfinfo with
  | Some (_, size) -> Some size
  | _ -> None


let get_struct_type_compinfo (ty: btype_t): bcompinfo_t =
  match bcfiles#resolve_type ty with
  | Ok ty ->
     (match ty with
      | TComp (ckey, _) -> bcfiles#get_compinfo ckey
      | _ ->
         raise
           (BCH_failure
              (LBLOCK [STR "Type is not a struct: "; btype_to_pretty ty])))
  | Error e ->
     raise
       (BCH_failure
          (LBLOCK [
               STR "Problem with type resolution in obtaining struct: ";
               STR (String.concat "; " e)]))


let get_compinfo_by_key (ckey: int): bcompinfo_t =
  bcfiles#get_compinfo ckey


let get_compinfo_field (c: bcompinfo_t) (fname: string): bfieldinfo_t =
  try
    List.find (fun finfo -> finfo.bfname = fname) c.bcfields
  with
  | Not_found ->
     raise
       (BCH_failure
          (LBLOCK [
               STR "Compinfo ";
               STR c.bcname;
               STR " does not have a field ";
               STR fname]))


let get_struct_field_at_offset
      (cinfo: bcompinfo_t) (offset: int): (bfieldinfo_t * int) option =
  let finfos = cinfo.bcfields in
  (* Some struct types may be incomplete and not have any fields at all *)
  if (List.length finfos) = 0 then
    None
  else
    let field0 = List.hd finfos in
    if offset = 0 then
      Some (field0, 0)
    else
      let field0type_r = resolve_type field0.bftype in
      let field0size_r = tbind size_of_btype field0type_r in
      match field0size_r with
      | Ok field0size ->
         if offset < field0size then
           Some (field0, offset)
         else
           List.fold_left (fun acc finfo ->
               match acc with
               | Some _ -> acc
               | _ ->
                  match finfo.bfieldlayout with
                  | Some (foffset, size) ->
                     if offset = foffset then
                       Some (finfo, 0)
                     else if offset > foffset && offset < foffset + size then
                       Some (finfo, offset - foffset)
                     else
                       None
                  | _ -> None) None finfos
      | Error e ->
         begin
           log_error
             "Unable to obtain struct field at offset for %s: %s [%s:%d]"
             cinfo.bcname
             (String.concat "; " e)
             __FILE__ __LINE__;
           None
         end


let is_sub_struct (ckey1: int) (ckey2: int) =
  let cinfo2 = get_compinfo_by_key ckey2 in
  let field0 = get_struct_field_at_offset cinfo2 0 in
  match field0 with
  | Some (bfinfo, 0) ->
     (match bfinfo.bftype with
      | TComp (i, _) -> ckey1 = i
      | _ -> false)
  | _ -> false


let rec get_compinfo_scalar_type_at_offset
          (cinfo: bcompinfo_t) (offset: int): btype_t option =
  let finfos = cinfo.bcfields in
  let field0 = List.hd finfos in
  let field0type_r = resolve_type field0.bftype in
  let field0size_r = tbind size_of_btype field0type_r in
  match field0type_r, field0size_r with
  | Error e, _
    | _, Error e ->
     begin
       log_error
         "Unable to get struct scalar type at offset for %s: %s [%s:%d]"
         cinfo.bcname
         (String.concat "; " e)
         __FILE__ __LINE__;
       None
     end
  | Ok field0type, Ok field0size ->
     if offset = 0 then
       if is_struct_type field0type then
         let subcinfo = get_struct_type_compinfo field0type in
         get_compinfo_scalar_type_at_offset subcinfo 0
       else
         Some field0type
     else if offset < field0size then
       if is_struct_type field0type then
         let subcinfo = get_struct_type_compinfo field0type in
         get_compinfo_scalar_type_at_offset subcinfo offset
       else
         None
     else
       List.fold_left (fun acc finfo ->
           match acc with
           | Some _ -> acc
           | _ ->
              match finfo.bfieldlayout with
              | Some (foffset, size) ->
                 let fieldtype = resolve_type finfo.bftype in
                 (match fieldtype with
                 | Error e ->
                    begin
                      log_error
                        "Problem with type resolution: %s [%s:%d]"
                        (String.concat "; " e)
                        __FILE__ __LINE__;
                      None
                    end
                 | Ok fieldtype ->
                    if offset = foffset then
                      if is_struct_type fieldtype then
                        let subcinfo = get_struct_type_compinfo fieldtype in
                        get_compinfo_scalar_type_at_offset subcinfo 0
                      else
                        Some fieldtype
                    else if offset > foffset && offset < foffset + size then
                      if is_struct_type fieldtype then
                        let subcinfo = get_struct_type_compinfo fieldtype in
                        get_compinfo_scalar_type_at_offset subcinfo (offset - foffset)
                      else
                        None
                    else
                      None)
              | _ ->
                 None) None finfos


let get_compinfo_struct_type (c: bcompinfo_t): btype_t = TComp (c.bckey, [])


let get_struct_type_fields (ty: btype_t): bfieldinfo_t list =
      if is_struct_type ty then
        let cinfo = get_struct_type_compinfo ty in
        let cinfo = layout_fields cinfo in
        cinfo.bcfields
      else
        []


let struct_field_categories (ty: btype_t): string list =
  match bcfiles#resolve_type ty with
  | Error e -> e
  | Ok ty ->
     match ty with
     | TArray (TComp (ckey, _), _, _)
     | TPtr (TPtr (TComp (ckey, _), _), _)
       | TPtr (TComp (ckey, _), _) ->
        let compinfo = bcfiles#get_compinfo ckey in
        List.map (fun f ->
            match f.bftype with
            | TInt _ -> "value"
            | TPtr (TInt _, _) -> "string"
            | TPtr (TFun _, _) -> "address"
            | _ -> "unknown") compinfo.bcfields

     | TArray ((TFun _ | TPtr (TFun _, _)), _, _) -> ["address"]

     | rty -> [btype_to_string ty; btype_to_string rty]


let struct_offset_field_categories (ty: btype_t): (int * string) list =
  match bcfiles#resolve_type ty with
  | Error e -> List.map (fun s -> (0, s)) e
  | Ok ty ->
     match ty with
     | TPtr (TPtr (TComp (ckey, _), _), _)
       | TPtr (TComp (ckey, _), _) ->
        let compinfo = bcfiles#get_compinfo ckey in
        List.map (fun f ->
            match f.bfieldlayout with
            | Some (offset, _) ->
               (match f.bftype with
                | TInt _ -> (offset, "value")
                | TPtr (TInt _, _) -> (offset, "string-address")
                | TArray (TInt _, _, _) -> (offset, "string")
                | _ -> (offset, "unknown"))
            | _ ->
               raise
                 (BCH_failure
                    (LBLOCK [
                         STR "Struct definition has no field layout: ";
                         STR (btype_to_string ty)]))) compinfo.bcfields
     | _ -> [(0, btype_to_string ty)]


let bexp_intconstant ?(ikind=IInt) (n: int) =
  let i64 = Int64.of_int n in
  Const (CInt (i64, ikind, None))
