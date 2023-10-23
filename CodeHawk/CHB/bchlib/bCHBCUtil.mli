(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2022 Aarno Labs LLC

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

(* chlib*)
open CHPretty

(* bchlib *)
open BCHBCTypes

val int_type_to_string: ikind_t -> string
val float_type_to_string: fkind_t -> string
val float_representation_to_string: frepresentation_t -> string

val attributes_to_string: b_attributes_t -> string
val exp_to_string: bexp_t -> string
val constant_to_string: bconstant_t -> string

val tname_to_string: tname_t -> string

val btype_to_string: btype_t -> string
val btype_to_pretty: btype_t -> pretty_t

val typ_compare: btype_t -> btype_t -> int

val btype_equal: btype_t -> btype_t -> bool

val add_attributes: btype_t -> b_attributes_t -> btype_t