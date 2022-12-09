(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022      Aarno Labs LLC

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

(* tchblib *)
open TCHSpecification

module TS = TCHTestSuite

module A = TCHAssertion
module G = TCHGenerator
module S = TCHSpecification

module BA = TCHBchlibAssertion
module BG = TCHBchlibGenerator
module BS = TCHBchlibSpecification

module D = BCHDoubleword


let testname = "bCHDoublewordTest"
let lastupdated = "2022-11-28"

let equal_dw = BA.equal_doubleword


let wordmaxm1 = D.string_to_doubleword "0xfffffffe"
let word1000 = D.string_to_doubleword "0x0000100"

let numzero = mkNumerical 0
let numnegone = mkNumerical (-1)


let doubleword_basic () =
  begin

    TS.new_testsuite (testname ^ "_basic") lastupdated;

    TS.add_simple_test
      ~title:"zero"
      (fun () ->
        A.equal_string "0x0" (D.string_to_doubleword "0x0")#to_hex_string);

    TS.add_simple_test
      ~title:"num-zero"
      (fun () ->
        A.equal_string "0x0" (D.numerical_to_doubleword numzero)#to_hex_string);

    TS.add_simple_test
      ~title:"num-neg-one"
      (fun () ->
        A.equal_string
          "0xffffffff" (D.numerical_to_doubleword numnegone)#to_hex_string);

    TS.add_simple_test
      ~title:"neg-one-signed"
      (fun () ->
        A.equal_string "-0x1" (D.numerical_to_signed_hex_string numnegone));

    TS.add_random_test
      ~title:"random"
      (G.make_int 0 BA.e32) (fun i -> (D.int_to_doubleword i)#to_hex_string)
      [S.always => BS.is_int_doublewordstring];

    TS.add_simple_test
      ~title:"add-zero"
      (fun () -> equal_dw D.wordzero (D.wordzero#add D.wordzero));

    TS.add_simple_test
      ~title:"add-max"
      (fun () -> equal_dw D.wordmax (D.wordzero#add D.wordmax));

    TS.add_simple_test
      ~title:"wrap-max"
      (fun () ->
        equal_dw
          ~msg:"addition wraps around" wordmaxm1 (D.wordmax#add D.wordmax));

    TS.add_simple_test
      ~title:"wrap-zero"
      (fun () ->
        let dw31 = D.int_to_doubleword BA.e31 in
        equal_dw ~msg:"addition wraps around" D.wordzero (dw31#add dw31));

    TS.add_random_test
      ~title:"msb"
      ~classifier:BG.msb_pair_classifier
      BG.doubleword_pair
      (fun (dw1, dw2) -> dw1#add dw2)
      [S.always => BS.is_sum_doubleword];

    TS.add_simple_test
      ~title:"subtract-zero"
      (fun () -> equal_dw D.wordzero (D.wordzero#subtract D.wordzero));

    TS.add_simple_test
      ~title:"subtract-max-zero"
      (fun () -> equal_dw D.wordmax (D.wordmax#subtract D.wordzero));

    TS.add_simple_test
      ~title:"subtract-max-max"
      (fun () -> equal_dw D.wordzero (D.wordmax#subtract D.wordmax));

    TS.add_simple_test
      ~title:"xor-max"
      (fun () -> equal_dw D.wordzero (D.wordmax#xor D.wordmax));

    TS.add_simple_test
      ~title:"xor-zero-max"
      (fun () -> equal_dw D.wordmax (D.wordzero#xor D.wordmax));

    TS.launch_tests ()
  end


let doubleword_assertions () =
  begin
    TS.new_testsuite (testname ^ "_assertions") lastupdated;

    TS.add_simple_test
      ~title:"hex-too-large"
      (fun () ->
        A.assertionfailure ~msg:"hex string is too large"
          (fun () -> ignore (D.string_to_doubleword "0xfffffffff")));

    TS.add_simple_test
      ~title:"subtract-no-wrap"
      (fun () ->
        A.raises ~msg:"subtraction does not wrap around"
          (fun () -> ignore (D.wordzero#subtract D.wordmax)));

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    doubleword_basic ();
    doubleword_assertions ();
    TS.exit_file ()
  end