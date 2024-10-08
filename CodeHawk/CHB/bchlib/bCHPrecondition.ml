(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHXmlDocument
open CHXmlReader

(* bchlib *)
open BCHBasicTypes
open BCHFtsParameter
open BCHBCTypePretty
open BCHBCTypes
open BCHBCTypeUtil
open BCHBCTypeXml
open BCHBTerm
open BCHCStructConstant
open BCHExternalPredicate
open BCHLibTypes
open BCHTypeDefinitions


let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [
        STR "(";
        INT node#getLineNumber;
        STR ",";
	INT node#getColumnNumber;
        STR ") ";
        msg] in
  begin
    ch_error_log#add "xml parse error" error_msg;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end

(* ----------------------------------------------------------------- read xml *)

let read_xml_par_preconditions
      (node:xml_element_int)
      (_thisf: bterm_t)
      (parameters: fts_parameter_t list): xxpredicate_t list =
  let one = IndexSize (NumConstant numerical_one) in
  let hasc = node#hasOneTaggedChild in
  let getc = node#getTaggedChild in
  let pNodes = if hasc "pre" then (getc "pre")#getChildren else [] in
  let parname = node#getAttribute "name" in
  let thispar =
    List.find (fun p -> (get_parameter_name p) = parname) parameters in
  let t = ArgValue thispar in
  let ty () =
    match BCHTypeDefinitions.resolve_type (get_parameter_type thispar) with
    | Ok (TFun _) -> get_parameter_type thispar
    | Ok (TPtr (t, _)) -> t
    | Ok (THandle (s, _)) -> TNamed (s, [])
    | _ ->
       match get_parameter_type thispar with
       | TFun _ -> get_parameter_type thispar
       | TPtr (t, _) -> t
       | THandle (s, _) -> TNamed (s, [])
       | _ ->
          raise_xml_error node
	    (LBLOCK [
                 STR "Pre: Expected pointer type for ";
                 STR (get_parameter_name thispar);
	         STR ", but found ";
                 btype_to_pretty (get_parameter_type thispar)]) in
  let getsize n typ =
    let has = n#hasNamedAttribute in
    let geti = n#getIntAttribute in
    if has "bytesize" then
      ByteSize (NumConstant (mkNumerical (geti "bytesize")))
    else if has "indexsize" then
      IndexSize (NumConstant (mkNumerical (geti "indexsize")))
    else match get_size_of_type typ with
    | Ok i -> NumConstant (mkNumerical i)
    | _ -> one in
  let aux node =
    match node#getTag with
    | "null-terminated" -> [XXNullTerminated t]
    | "not-null" -> [XXNotNull t]
    | "null" -> [XXNull t]
    | "deref-read" ->
       let typ = ty () in
       [XXBuffer (typ, t, getsize node typ);
        XXInitializedRange (typ, t, getsize node typ);
        XXNotNull t;]
    | "deref-read-nt" ->
       let typ = ty () in
       [XXBuffer (typ, t, ArgNullTerminatorPos t);
        XXInitializedRange (typ, t, ArgNullTerminatorPos t);
        XXNotNull t;
        XXNullTerminated t]
    | "deref-read-null" ->
       let typ = ty () in
       [XXBuffer (typ, t, getsize node typ);
        XXInitializedRange (typ, t, ArgNullTerminatorPos t)]
    | "deref-read-null-nt" ->
       let typ = ty () in
       [XXBuffer (typ, t, ArgNullTerminatorPos t);
        XXInitializedRange (typ, t, ArgNullTerminatorPos t);
        XXNullTerminated t]
    | "deref-write" ->
       let typ = ty () in
       [XXBuffer (typ, t, getsize node typ); XXNotNull t]
    | "deref-write-null" ->
       let typ = ty () in
       [XXBuffer (typ, t, getsize node typ)]
    | "allocation-base" -> [XXAllocationBase t]
    | "function-pointer" ->
       let typ = ty () in [XXFunctionPointer (typ, t)]
    | "format-string" -> [XXOutputFormatString t]
    | "includes" ->
      let name = node#getAttribute "name" in
      [XXIncludes (t,get_structconstant name)]
    | "enum-value" ->
       let flags =
         node#hasNamedAttribute "flags"
         && (node#getAttribute "flags") = "true" in
       [XXEnum (t, node#getAttribute "name", flags)]
    | "non-negative"
      | "nonnegative" -> [XXNonNegative t]
    | "positive" -> [XXPositive t]
    | s ->
       raise_xml_error node
         (LBLOCK [
              STR "Parameter precondition ";
              STR s;
              STR " not recognized"]) in
  List.concat (List.map aux pNodes)


let read_xml_precondition_xxpredicate
      (node: xml_element_int)
      (thisf: bterm_t)
      (parameters: fts_parameter_t list): xxpredicate_t list =
  let gt n = read_xml_bterm n thisf parameters in
  let gty = read_xml_type in
  let rec aux node =
    let cNodes = node#getChildren in
    let pNode = List.hd cNodes in
    let argNodes = List.tl cNodes in
    let arg n =
      try
        List.nth argNodes n
      with
      | Failure _ ->
         raise_xml_error
           node
           (LBLOCK [STR "Expected "; INT (n+1); STR " arguments"]) in
    if is_relational_operator pNode#getTag then
      let op = get_relational_operator pNode#getTag in
      [XXRelationalExpr (op, gt (arg 0), gt (arg 1))]
    else
      match pNode#getTag with
      | "or" -> [XXDisjunction (List.concat (List.map aux argNodes))]
      | "implies" ->
         [XXConditional (List.hd (aux (arg 0)), List.hd (aux (arg 1)))]
      | "not-null" -> [XXNotNull (gt (arg 0))]
      | "null" -> [XXNull (gt (arg 0))]
      | "null-terminated" -> [XXNullTerminated (gt (arg 0))]
      | "format-string" -> [XXOutputFormatString (gt (arg 0))]
      | "allocation-base" -> [XXAllocationBase (gt (arg 0))]
      | "function-pointer" -> [XXFunctionPointer (gty(arg 0), gt (arg 1))]
      | "enum-value" ->
	let flags =
	  (pNode#hasNamedAttribute "flags")
          && (pNode#getAttribute "flags") = "true" in
	[XXEnum (gt (arg 0), pNode#getAttribute "name", flags)]
      | "includes" ->
	let sc = read_xml_cstructconstant (pNode#getTaggedChild "sc") in
	[XXIncludes (gt (arg 0), sc)]
      | "deref-read" | "block-read" ->
	 [XXBuffer (gty (arg 0), gt (arg 1), gt (arg 2));
          XXNotNull (gt (arg 1))]
      | "deref-read-null" -> [XXBuffer (gty (arg 0), gt (arg 1), gt (arg 2))]
      | "deref-read-nt" ->
	let dest = gt (arg 1) in
	let len = ArgNullTerminatorPos dest in
	[XXBuffer (gty (arg 0), dest, len); XXNotNull dest]
      | "deref-read-nt-null" ->
	let dest = gt (arg 1) in
	let len = ArgNullTerminatorPos dest in
	[XXBuffer (gty (arg 0), dest, len)]
      | "deref-write" ->
         let dest = gt (arg 1) in
	 [XXBlockWrite (gty (arg 0), dest, gt (arg 2)); XXNotNull dest]
      | "deref-write-null" ->
	[XXBlockWrite (gty (arg 0), gt (arg 1), gt (arg 2))]
      | s ->
         raise_xml_error
           node
	   (LBLOCK [
                STR "Precondition predicate symbol ";
                STR s;
                STR " not recognized"]) in
  aux node


let read_xml_precondition
      (node: xml_element_int)
      (thisf: bterm_t)
    (parameters: fts_parameter_t list): xxpredicate_t list =
  read_xml_precondition_xxpredicate
    ((node#getTaggedChild "math")#getTaggedChild "apply") thisf parameters


let read_xml_preconditions
      (node:xml_element_int)
      (thisf: bterm_t)
      (parameters: fts_parameter_t list): xxpredicate_t list =
  let getcc = node#getTaggedChildren in
  List.concat
    (List.map
       (fun n ->
         read_xml_precondition n thisf parameters) (getcc "pre"))


let make_attribute_preconditions
      (attrs: precondition_attribute_t list)
      (parameters: fts_parameter_t list): xxpredicate_t list =
  let get_par (n: int) =
    try
      List.find (fun p ->
          match p.apar_index with Some ix -> ix = n | _ -> false) parameters
    with
    | Not_found ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "No parameter with index ";
                 INT n;
	         pretty_print_list (List.map (fun p -> p.apar_name) parameters)
	           (fun s -> STR s) "[" "," "]" ])) in
  let get_derefty (par: fts_parameter_t): btype_t =
    if is_pointer par.apar_type then
      ptr_deref par.apar_type
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "parameter is not a pointer type: ";
                fts_parameter_to_pretty par])) in
  List.fold_left (fun acc attr ->
      match attr with
      | (APCReadOnly (n, None)) ->
         let par = get_par n in
         let ty = get_derefty par in
         (XXBuffer (ty, ArgValue par, RunTimeValue)) :: acc
      | (APCWriteOnly (n, None)) ->
         let par = get_par n in
         let ty = get_derefty par in
         (XXBlockWrite (ty, ArgValue par, RunTimeValue)) :: acc
      | _ -> acc) [] attrs
