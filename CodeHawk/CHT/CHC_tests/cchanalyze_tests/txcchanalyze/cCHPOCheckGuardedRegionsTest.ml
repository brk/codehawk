(* An output region is conditional on its exact call result, bounded and live. *)
open CCHBasicTypes
open CCHPreTypes
open CCHLibTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils
let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PGuardedRegions";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PGuardedRegions" "guarded_regions");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do ignore (CCHGenerateAndCheck.generate_and_check_process_file domains) done;
  let reads name =
    let result = List.filter (fun po -> match po#get_predicate with
        | PInitialized (Var ("v", _), _) -> true | _ -> false)
        (proof_scaffolding#get_proof_obligations name) in
    if result = [] then failwith (name ^ ": missing copied read"); result in
  List.iter (fun name -> List.iter (fun po ->
      if not po#is_safe || po#is_violation then failwith (CU.located_po_to_string po);
      match po#get_dependencies with
      | Some (DEnvC (_, assumptions)) when List.exists (function
          | PostAssumption (_, XBufferOnReturn (Ge, n, ArgAddressedValue _, _)) -> n#is_zero
          | _ -> false) assumptions -> ()
      | _ -> failwith (name ^ ": guarded region dependency omitted")) (reads name))
    ["region_good"; "region_descriptor_good"; "region_offset_good";
     "region_readonly_good"; "region_saved_good"; "region_widened_good";
     "region_after_release_good"; "region_before_release_good"];
  List.iter (fun name -> List.iter (fun po ->
      if po#is_safe then failwith (name ^ ": unsafe/unsupported copied read proved")) (reads name))
    ["region_partial_bad"; "region_failure_bad"; "region_unguarded_bad";
     "region_uncleared_bad"; "region_released_bad"; "region_reclear_bad";
     "region_opaque_bad"; "region_reacquire_bad"; "region_old_alias_bad";
     "region_oversized_bad"; "region_beyond_bad"; "region_other_guard_bad";
     "region_changed_status_bad"; "region_truncated_status_bad";
     "region_wrong_slot_bad"; "region_missing_slot_bad"; "region_branch_bad";
     "region_nested_unknown"; "region_zero_bad"; "region_variable_unknown";
     "region_two_clears_unknown"; "region_loop_unknown"; "region_indirect_bad";
     "region_slot_escape_bad"; "region_descriptor_growth_bad"];
  List.iter (fun name ->
      let entries = List.filter (fun po -> match po#get_predicate with
          | PInitialized (Var ("raw", _), _) -> true | _ -> false)
          (proof_scaffolding#get_proof_obligations name) in
      if entries = [] || List.exists (fun po -> po#is_safe) entries then
        failwith (name ^ ": output identity falsely initialized the failed slot"))
    ["region_failure_bad"; "region_unguarded_bad"];
  CU.analysis_take_down "guarded_regions";
  print_endline "guarded regions: eight conditional reads; 25 unsafe/unsupported reads remain open"
