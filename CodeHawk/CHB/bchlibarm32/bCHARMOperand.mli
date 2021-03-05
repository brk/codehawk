(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021 Aarno Labs, LLC

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
open CHNumerical
open CHLanguage

(* chutil *)
open CHXmlDocument

(* xprlib *)
open Xprt

(* bchlib *)
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMTypes

val arm_operand_mode_to_string: arm_operand_mode_t -> string

val armreg_to_string: arm_reg_t -> string

val arm_register_op: arm_reg_t -> arm_operand_mode_t -> arm_operand_int

val arm_register_list_op: arm_reg_t list -> arm_operand_mode_t -> arm_operand_int

val arm_immediate_op: immediate_int -> arm_operand_int

val arm_absolute_op: doubleword_int -> arm_operand_mode_t -> arm_operand_int

val mk_arm_shifted_register_op:
  arm_reg_t
  -> int (* shifttype *)
  -> int (* shiftamount *)
  -> arm_operand_mode_t
  -> arm_operand_int

val mk_arm_immediate_op:
  bool (* signed *)
  -> int (* size in bytes *)
  -> numerical_t (* value *)
  -> arm_operand_int

val mk_arm_absolute_target_op:
  pushback_stream_int
  -> doubleword_int
  -> int
  -> arm_operand_mode_t
  -> arm_operand_int

val mk_arm_offset_address_op:
  arm_reg_t
  -> int     (* nonnegative offset *)
  -> bool    (* isadd *)
  -> bool    (* iswback *)
  -> bool    (* isindex *)
  -> arm_operand_mode_t
  -> arm_operand_int