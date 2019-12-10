(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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
open CHPretty
open CHLanguage
open CHNumericalConstraints

(* bchlib *)
open BCHLibTypes
open BCHUtilities

let version_date = BCHUtilities.get_date_and_time ()
let get_version () = version_date

exception BCH_failure of pretty_t 

exception Internal_error of string
exception Invocation_error of string
exception Invalid_input of string

exception Request_function_retracing       (* raised when control flow is found to be altered *)

let eflags_to_string_table = Hashtbl.create 6
let eflags_from_string_table = Hashtbl.create 6

let _ =
  List.iter (fun (e,s) ->
      add_to_sumtype_tables eflags_to_string_table eflags_from_string_table e s)
	    [ (OFlag, "OF") ;
	      (CFlag, "CF") ;
	      (ZFlag, "ZF") ;
	      (SFlag, "SF") ;
	      (PFlag, "PF") ;
	      (DFlag, "DF") ;
	      (IFlag, "IF") ]
  
let eflag_to_string (e:eflag_t) = 
  get_string_from_table "eflags_to_string_table" eflags_to_string_table e

let eflag_from_string (name:string) =
  get_sumtype_from_table "eflags_from_string_table" eflags_from_string_table name

let eflag_compare (f1:eflag_t) (f2:eflag_t) = 
  Pervasives.compare (eflag_to_string f1) (eflag_to_string f2)

type risk_type_t =
  | OutOfBoundsRead
  | OutOfBoundsWrite
  | NullDereference
  | TypeConditionViolation
  | FunctionFailure
  
let risk_types_to_string_table = Hashtbl.create 5
let risk_types_from_string_table = Hashtbl.create 5

let _ = List.iter (fun (r,s) -> 
  add_to_sumtype_tables risk_types_to_string_table risk_types_from_string_table r s)
  [ (OutOfBoundsRead, "OBR") ;
    (OutOfBoundsWrite, "OBW" ) ;
    (NullDereference, "NDR" ) ;
    (TypeConditionViolation, "TCV") ;
    (FunctionFailure, "FAIL") ]
  
let risk_type_to_string (r:risk_type_t) = 
  get_string_from_table "risk_types_to_string_table" risk_types_to_string_table r
    
let risk_type_from_string (s:string) =
  get_sumtype_from_table "risk_types_from_string_table" risk_types_from_string_table s
    
let variable_to_pretty v = STR v#getName#getBaseName
let symbol_to_pretty s   = STR s#getBaseName
let factor_to_pretty f   = variable_to_pretty f#getVariable
  
let variable_to_string v = v#getName#getBaseName
let symbol_to_string s   = s#getBaseName
let factor_to_string f   = variable_to_string f#getVariable
  
  
