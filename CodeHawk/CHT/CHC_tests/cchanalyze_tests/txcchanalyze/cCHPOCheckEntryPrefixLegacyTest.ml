(* Missing parser certificates cannot support an entry-byte frame. *)
open CCHPreTypes
open CCHProofScaffolding

module CU = TCHCchanalyzeUtils

let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PEntryPrefixLegacy";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PEntryPrefixLegacy" "entry_prefix_legacy");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do
    ignore (CCHGenerateAndCheck.generate_and_check_process_file domains)
  done;
  List.iter (fun name ->
      let ranges = List.filter (fun po -> match po#get_predicate with
          | PInitializedRange _ -> true | _ -> false)
          (proof_scaffolding#get_proof_obligations name) in
      if ranges = [] then failwith (name ^ ": missing source requirement");
      List.iter (fun po ->
          if po#is_safe then failwith (name ^ ": " ^ CU.located_po_to_string po)) ranges)
    ["pure_copy"; "read_before_event"; "dirty_returning_path";
     "formal_replaced_after_copy"; "event_after_copy"; "bounded_field_before_event"];
  CU.analysis_take_down "entry_prefix_legacy";
  print_endline "entry prefixes: missing certificates leave source requirements open"
