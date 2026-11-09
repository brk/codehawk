(* Regression tests use parser inputs, not cached proof results. Unsafe controls
   are analyzed only; none of their deliberately invalid C paths is executed. *)
open CCHPreTypes
open CCHProofScaffolding

module CU = TCHCchanalyzeUtils

let destination_read (po: proof_obligation_int) =
  match po#get_predicate with
  | PInitialized (CCHBasicTypes.Var (("dest" | "datum"), _), _) -> true
  | _ -> false

let check filename good bad =
  let summaries_jar = Some "testinputs/PErrnoWritten/cchsummaries.jar" in
  ignore (CU.analysis_setup ~summaries_jar "PInitialized" filename);
  (* Match project analysis's five refinement rounds. A local count's value
     becomes available to the call translator through the previous round. *)
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain;
      sym_pointersets_domain] in
  for _round = 2 to 5 do
    ignore (CCHGenerateAndCheck.generate_and_check_process_file domains)
  done;
  List.iter (fun (name, expected_safe) ->
      let reads = List.filter destination_read
          (proof_scaffolding#get_proof_obligations name) in
      if reads = [] then failwith (name ^ ": destination read was not analyzed");
      List.iter (fun po ->
          if po#is_safe <> expected_safe || po#is_violation then
            failwith (name ^ ": " ^ CU.located_po_to_string po)) reads;
      if List.mem name ["copy_scalar_bad"; "copy_then_initialize_bad";
          "copy_branch_bad"; "copy_small_union_bad"; "copy_array_bad";
          "copy_chain_bad"; "copy_overwritten_array_bad";
          "copy_unknown_write_bad"; "copy_indirect_write_bad"]
         || (filename = "sb_received_bytes" && not expected_safe) then
        List.iter (fun po -> match po#get_predicate with
            | PInitializedRange _ when po#is_safe ->
               failwith (name ^ ": uninitialized source range was marked safe")
            | _ -> ()) (proof_scaffolding#get_proof_obligations name))
    ((List.map (fun n -> n, true) good) @ (List.map (fun n -> n, false) bad));
  if filename = "memcpy_initialization" then
    if not (List.exists (fun po -> po#is_violation)
              (proof_scaffolding#get_proof_obligations "copy_bounds_bad")) then
      failwith "out-of-bounds copy was no longer flagged";
  CU.analysis_take_down filename

let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  check "memcpy_initialization"
    ["copy_scalar_good"; "copy_union_good"; "copy_float_good"]
    ["copy_scalar_bad"; "copy_partial_bad"];
  check "memcpy_ranges"
    ["copy_then_change_good"; "copy_branch_good"; "copy_array_good";
     "copy_local_count_good"]
    ["copy_then_initialize_bad"; "copy_branch_bad"; "copy_zero_bad";
     "copy_wider_bad"; "copy_small_union_bad"; "copy_array_bad";
     "copy_chain_bad"; "copy_late_count_bad"; "copy_tail_field_bad";
     "copy_array_tail_bad"; "copy_overwritten_array_bad";
     "copy_unknown_write_bad"; "copy_indirect_write_bad"];
  check "sb_received_bytes"
    ["received_local_good"; "received_typed_stride_good";
     "received_nested_offset_good"; "received_composed_offset_good"]
    ["header_only_truncated_bad"; "capacity_without_initialization_bad";
     "missing_last_byte_bad"; "zero_before_overwrite_bad";
     "unknown_producer_bad"; "receive_without_contract_bad";
     "next_receive_without_frame_bad"; "explicitly_released_bad";
     "offset_missing_last_byte_bad"; "typed_stride_truncated_bad";
     "negative_offset_bad"; "one_past_source_bad"];
  print_endline "memcpy initialization: 11 positive, 27 negative and 1 bounds control passed"
