(* Normal-return aliases must not erase a documented nullable error return. *)
open CCHBasicTypes
open CCHPreTypes
open CCHProofScaffolding
module CU=TCHCchanalyzeUtils
let ()=
 CCHSettings.system_settings#set_wordsize 64;
 CCHSettings.system_settings#set_undefined_behavior_analysis;
 CCHSettings.system_settings#set_contractpath "testinputs/PNullableAlias";
 ignore(CU.analysis_setup ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar") "PNullableAlias" "nullable_alias");
 let domains=CCHInvariantFact.[linear_equalities_domain;pepr_domain;valueset_domain;intervals_domain;symbolic_sets_domain;sym_pointersets_domain] in
 for _round=2 to 5 do ignore(CCHGenerateAndCheck.generate_and_check_process_file domains) done;
 let checks name=let xs=List.filter(fun po->match po#get_predicate with PNotNull(Lval(Var("p",_),NoOffset))->true|_->false)(proof_scaffolding#get_proof_obligations name) in
   if xs=[] then failwith(name^": missing pointer check");xs in
 List.iter(fun name->List.iter(fun po->if po#is_safe then failwith(name^": nullable return incorrectly proved nonnull"))(checks name))
   ["fgets_unchecked_bad";"fgets_other_guard_bad";"fgets_failed_bad";"fgets_guarded_good"];
 List.iter(fun name->List.iter(fun po->if not po#is_safe || po#is_violation then failwith(CU.located_po_to_string po))(checks name))
   ["memcpy_alias_good";"memset_alias_good"];
 CU.analysis_take_down "nullable_alias";
 print_endline "nullable aliases: unsafe normal-only proofs reopened; unconditional copy/clear aliases retained"
