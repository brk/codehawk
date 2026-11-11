(* Selector correlation proves local bytes, never a table image or earlier read. *)
open CCHBasicTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils

let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PCorrelatedUnion";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PCorrelatedUnion" "correlated_union_bytes");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do ignore (CCHGenerateAndCheck.generate_and_check_process_file domains) done;
  let query name variable =
    match List.filter (fun po -> match po#get_predicate with
        | PInitializedRange (AddrOf (Var (v, _), NoOffset), _) -> v = variable
        | _ -> false) (proof_scaffolding#get_proof_obligations name) with
    | [po] -> po
    | _ -> failwith (name ^ ": expected exactly one local range for " ^ variable) in
  List.iter (fun name ->
      let po = query name "value" in
      if not po#is_safe || po#get_dependencies <> Some (DLocal []) then
        failwith (name ^ ": missing structural selector/byte proof"))
    ["correlated_parameter"; "correlated_global"; "descriptor_copy";
     "multiple_query_cases"; "first_fallthrough_full"; "constant_default"; "case_range"];
  List.iter (fun name ->
      if (query name "value")#is_safe then failwith (name ^ ": invalid frame proved"))
    ["changed_selector"; "opaque_selector"; "short_member";
     "dirty_query_fallthrough"; "merged_query_labels"; "wrong_case_width";
     "changed_via_alias"; "volatile_selector"; "volatile_descriptor"; "changed_index";
     "escaped_address"; "stored_address"; "partial_overwrite"; "uninitialized_switch_word";
     "opaque_before_reads"; "loop_selector"; "goto_selector"; "asm_selector";
     "nested_result"; "copied_selector"; "copied_pointer_selector";
     "converted_case_label"; "reverse_case_conversion"];
  let other = query "descriptor_copy" "other" in
  (match other#get_dependencies with
   | Some (DReduced (_, [LocalAssumption (PInitializedRange _ as predicate)]))
        when other#is_safe ->
      let sources = List.filter (fun po -> po#get_predicate = predicate)
          (proof_scaffolding#get_spo_manager "descriptor_copy")#get_spos in
      if List.length sources <> 1 || List.exists (fun po -> po#is_safe) sources then
        failwith "descriptor_copy: table source initialized"
   | _ -> failwith "descriptor_copy: other local lost its original source dependency");
  let uninitialized_source name =
    let sources = List.filter (fun po -> match po#get_predicate with
        | PInitialized (Var ("unknown", _), NoOffset) -> true | _ -> false)
        (proof_scaffolding#get_proof_obligations name) in
    if List.length sources <> 1 || List.exists (fun po -> po#is_safe) sources then
      failwith (name ^ ": earlier uninitialized source requirement lost") in
  List.iter uninitialized_source ["uninitialized_member"; "uninitialized_switch_word"; "caller_uninitialized"];
  CU.analysis_take_down "correlated_union_bytes";
  print_endline "correlated union bytes: seven structural proofs, twenty-three open frames, source requirements retained"
