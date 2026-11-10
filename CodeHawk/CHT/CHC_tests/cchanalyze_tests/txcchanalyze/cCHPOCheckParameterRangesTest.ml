(* Check byte-range entry predicates against the historical clear extent. *)
open CCHLibTypes
open CCHPreTypes
open CCHProofScaffolding

module CU = TCHCchanalyzeUtils

let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PParameterRanges";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PParameterRanges" "parameter_ranges");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do
    ignore (CCHGenerateAndCheck.generate_and_check_process_file domains)
  done;
  let ranges name =
    let selected = List.filter (fun po -> match po#get_predicate with
        | PInitializedRange _ -> true
        | _ -> false) (proof_scaffolding#get_proof_obligations name) in
    if selected = [] then failwith (name ^ ": initialized-range obligation missing");
    selected in
  let conditional po =
      match po#get_dependencies with
      | Some (DEnvC (invariants, assumptions)) when po#is_safe && not po#is_violation
          && invariants <> []
          && List.exists (function PostAssumption (_, XBufferOnReturn _) -> true
                                | _ -> false) assumptions -> ()
      | _ -> failwith (CU.located_po_to_string po) in
  List.iter (fun name -> List.iter conditional (ranges name))
    ["full_clear"; "captured_count"; "bounded_prefix"; "constant_clear"];
  List.iter (fun name ->
      if List.exists (fun po -> po#is_safe) (ranges name) then
        failwith (name ^ ": range was incorrectly accepted"))
    ["independent_counts"; "changed_count"; "short_branch"; "expired_region";
     "opaque_writer"; "wrapping_bound"; "signed_count"; "word_count_is_not_bytes"];
  CU.analysis_take_down "parameter_ranges";
  print_endline "parameter ranges: four conditional ranges and eight open controls"
