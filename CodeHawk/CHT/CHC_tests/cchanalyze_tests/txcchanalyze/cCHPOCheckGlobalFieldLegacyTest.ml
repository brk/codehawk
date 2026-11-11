open CCHBasicTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils

let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PGlobalFieldLegacy";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PGlobalFieldLegacy" "global_field_legacy");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do ignore (CCHGenerateAndCheck.generate_and_check_process_file domains) done;
  List.iter (fun name ->
      let found = List.filter (fun po -> match po#get_predicate with
          | PInitialized (Var (variable, _), _) -> List.mem variable ["result"; "first"; "second"]
          | _ -> false)
          (proof_scaffolding#get_proof_obligations name) in
      if found = [] || List.exists (fun po -> po#is_safe) found then
        failwith (name ^ ": missing parser certificate accepted"))
    ["comparison"; "changed_global_before"; "changed_global_after"; "two_images"];
  CU.analysis_take_down "global_field_legacy";
  print_endline "global field copies: missing parser certificates retain open reads"
