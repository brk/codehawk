(* Explicitly conditional malloc-region bytes and independent lifetime facts. *)
open CCHBasicTypes
open CCHLibTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils
let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PAllocatedBytes";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PAllocatedBytes" "allocated_bytes");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do ignore (CCHGenerateAndCheck.generate_and_check_process_file domains) done;
  let reads name =
    let rs = List.filter (fun po -> match po#get_predicate with
        | PInitialized (Var ("value", _), _) -> true | _ -> false)
        (proof_scaffolding#get_proof_obligations name) in
    if rs = [] then failwith (name ^ ": copied read missing"); rs in
  let conditional po =
    if not po#is_safe || po#is_violation then failwith (CU.located_po_to_string po);
    match po#get_dependencies with
    | Some (DEnvC (_, assumptions)) ->
       if not (List.exists (function PostAssumption (_, XNewMemory ReturnValue) -> true | _ -> false) assumptions)
          || not (List.exists (function PostAssumption (_, XBuffer (ReturnValue, _)) -> true | _ -> false) assumptions) then
         failwith "allocation identity/capacity dependency omitted"
    | _ -> failwith "allocation proof became unconditional" in
  List.iter (fun name -> List.iter conditional (reads name))
    ["heap_full_good"; "heap_typed_offset_good"; "heap_byte_offset_good";
     "heap_descriptor_good"; "heap_entry_good"; "heap_before_free_good";
     "heap_captured_good"; "heap_readonly_good"];
  List.iter (fun name -> List.iter (fun po ->
      if po#is_safe then failwith (name ^ ": allocation bytes/lifetime invented")) (reads name))
    ["heap_partial_bad"; "heap_failed_bad"; "heap_free_bad"; "heap_uncleared_bad";
     "heap_reassign_bad"; "heap_opaque_bad"; "heap_overwrite_bad";
     "heap_other_clear_unknown"; "heap_nonnull_other_bad"; "heap_short_alloc_bad";
     "heap_oversized_clear_bad"; "heap_beyond_bad"; "heap_wrong_stride_bad";
     "heap_partial_field_unknown"; "heap_arithmetic_slot_unknown";
     "heap_realloc_unknown"; "heap_reuse_bad"; "heap_external_allocator_unknown";
     "heap_no_guard_unknown"; "heap_nested_slot_unknown"; "heap_integer_cast_unknown";
     "heap_zero_unknown"; "heap_external_unknown"; "heap_two_clears_unknown";
     "heap_size_captured_unknown"; "heap_reclear_after_free_bad";
     "heap_opaque_reclear_unknown"; "heap_entry_beyond_bad";
     "heap_indirect_reclear_unknown"; "heap_escaped_slot_unknown";
     "heap_branch_live_bad"; "heap_loop_unknown"; "heap_field_wide_bad"];
  List.iter (fun name ->
      let ranges = List.filter (fun po -> match po#get_predicate with
          | PInitializedRange _ -> true | _ -> false)
          (proof_scaffolding#get_proof_obligations name) in
      if ranges = [] then failwith (name ^ ": initialized source entry missing");
      List.iter conditional ranges)
    ["heap_full_good"; "heap_typed_offset_good"; "heap_descriptor_good"; "heap_entry_good"];
  CU.analysis_take_down "allocated_bytes";
  print_endline "allocated bytes: explicit malloc dependencies, exact intervals and non-resurrecting lifetime passed"
