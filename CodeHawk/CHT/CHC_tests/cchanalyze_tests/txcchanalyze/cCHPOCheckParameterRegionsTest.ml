(* An allocation and its clear retain their respective by-value counts. *)
open CCHBasicTypes
open CCHLibTypes
open CCHPreTypes
open CCHProofScaffolding

module CU = TCHCchanalyzeUtils

let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PParameterRegions";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PParameterRegions" "parameter_regions");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do
    ignore (CCHGenerateAndCheck.generate_and_check_process_file domains)
  done;
  let reads name =
    let selected = List.filter (fun po -> match po#get_predicate with
        | PInitialized (Var ("value", _), _) -> true
        | _ -> false) (proof_scaffolding#get_proof_obligations name) in
    if selected = [] then failwith (name ^ ": copied read missing");
    selected in
  let conditional po = match po#get_dependencies with
    | Some (DEnvC (invariants, assumptions)) when po#is_safe && not po#is_violation
        && invariants <> []
        && List.exists (function PostAssumption (_, XBufferOnReturn _) -> true | _ -> false) assumptions -> ()
    | _ -> failwith (CU.located_po_to_string po) in
  List.iter (fun name -> List.iter conditional (reads name))
    ["same_parameter"; "constant_slot"; "bounded_prefix"; "smaller_clear";
     "overwrite_count_after_clear"];
  List.iter (fun name -> List.iter (fun po -> if po#is_safe then
      failwith (name ^ ": invalid or unsupported count was accepted")) (reads name))
    ["different_counts"; "larger_clear"; "short_parameter"; "release_before_clear";
     "inflate_after_short_clear"; "signed_conversion"; "mismatched_status";
     "one_short_branch"; "addressed_count"; "wrapping_count"; "wrapping_guard"];
  CU.analysis_take_down "parameter_regions";
  print_endline "parameter regions: five conditional copies and eleven open controls"
