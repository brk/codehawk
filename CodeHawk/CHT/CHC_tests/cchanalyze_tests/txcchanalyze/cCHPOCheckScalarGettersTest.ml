(* Read-only integer metadata getters capture values, never object capacity. *)
open CCHBasicTypes
open CCHPreTypes
open CCHLibTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils
let () =
 CCHSettings.system_settings#set_wordsize 64;
 CCHSettings.system_settings#set_undefined_behavior_analysis;
 CCHSettings.system_settings#set_contractpath "testinputs/PScalarGetters";
 ignore(CU.analysis_setup ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar") "PScalarGetters" "scalar_getters");
 let domains=CCHInvariantFact.[linear_equalities_domain;pepr_domain;valueset_domain;intervals_domain;symbolic_sets_domain;sym_pointersets_domain] in
 for _round=2 to 5 do ignore(CCHGenerateAndCheck.generate_and_check_process_file domains) done;
 let pos name=proof_scaffolding#get_proof_obligations name in
 let reads name=let xs=List.filter(fun po->match po#get_predicate with PInitialized(Var("value",_),_)->true|_->false)(pos name) in
   if xs=[] then failwith(name^": missing copied read");xs in
 List.iter(fun name->List.iter(fun po->
   if not po#is_safe || po#is_violation then failwith(CU.located_po_to_string po);
   match po#get_dependencies with
   | Some(DEnvC(_,deps)) when List.exists(function PostAssumption(_,XPreservesAllMemory)->true|_->false)deps
       && List.exists(function PostAssumption(_,XRelationalExpr(Eq,ReturnValue,ArgAddressedValue _))->true|_->false)deps->()
   | _->failwith(name^": scalar alias/frame dependency lost"))(reads name))
   ["scalar_length_good";"scalar_captured_good";"scalar_heap_good"];
 List.iter(fun name->List.iter(fun po->if po#is_safe then failwith(name^": unsafe/unsupported read proved"))(reads name))
   ["scalar_zero_bad";"scalar_short_bad";"scalar_oversized_bad";"scalar_missing_bad";"scalar_opaque_bad";
    "scalar_post_only_unknown";"scalar_union_unknown";"scalar_volatile_unknown";"scalar_nested_unknown";
    "scalar_released_bad";"scalar_float_unknown";"scalar_bool_bad"];
 let entries=List.filter(fun po->match po#get_predicate with PInitialized(_,Field(("capacity",_),NoOffset))->true|_->false)(pos "scalar_missing_bad") in
 if entries=[] || List.exists(fun po->po#is_safe)entries then failwith "getter supplied missing entry metadata";
 CU.analysis_take_down "scalar_getters";
 print_endline "scalar getters: three conditional clear/read proofs; twelve controls remain open"
