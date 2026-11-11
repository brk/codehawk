(* Missing parser layout/scope certificates cannot invent entry-byte facts. *)
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils

let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PParameterEntryLegacy";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PParameterEntryLegacy" "parameter_entry_legacy");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do
    ignore (CCHGenerateAndCheck.generate_and_check_process_file domains)
  done;
  List.iter (fun name ->
      let found = List.filter (fun po -> match po#get_predicate with
          | PInitializedRange _ -> true | _ -> false)
          (proof_scaffolding#get_proof_obligations name) in
      if found = [] then failwith (name ^ ": missing source requirement");
      List.iter (fun po -> if po#is_safe then
          failwith (name ^ ": missing certificate accepted: " ^ CU.located_po_to_string po)) found)
    ["scalar_copy"; "union_copy"; "read_before_event"; "before_switch";
     "formal_replaced_after"; "event_after_copy"; "short_copy"];
  CU.analysis_take_down "parameter_entry_legacy";
  print_endline "parameter entry inference: missing certificates remain open"
