open CCHBasicTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils

let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PCorrelatedUnionLegacy";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PCorrelatedUnionLegacy" "correlated_union_legacy");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do ignore (CCHGenerateAndCheck.generate_and_check_process_file domains) done;
  List.iter (fun name ->
      let ranges = List.filter (fun po -> match po#get_predicate with
          | PInitializedRange (AddrOf (Var ("value", _), NoOffset), _) -> true
          | _ -> false) (proof_scaffolding#get_proof_obligations name) in
      if List.length ranges <> 1 || List.exists (fun po -> po#is_safe) ranges then
        failwith (name ^ ": missing parser certificates accepted"))
    ["correlated_parameter"; "correlated_global"; "descriptor_copy";
     "multiple_query_cases"; "first_fallthrough_full"; "constant_default"; "case_range"];
  CU.analysis_take_down "correlated_union_legacy";
  print_endline "correlated union bytes: missing certificates retain open requirements"
