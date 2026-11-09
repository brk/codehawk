(* Guarded guarantees remain conditional and refer to the same immutable call. *)
open CCHBasicTypes
open CCHLibTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils
let () =
  List.iter (fun op ->
      let pc = XInitializedOnReturn (op, CHNumerical.mkNumerical (-7),
          ArgAddressedValue (ArgValue (ParFormal 1, ArgNoOffset), ArgNoOffset)) in
      let node = CHXmlDocument.xmlElement "post" in
      CCHExternalPredicate.write_xmlx_xpredicate node ["out", 1] pc;
      let restored = CCHExternalPredicate.read_xml_xpredicate (node#getTaggedChild "math") ["out", 1] in
      let id = CCHInterfaceDictionary.interface_dictionary in
      let indexed = id#get_xpredicate (id#index_xpredicate pc) in
      let repr = CCHExternalPredicate.xpredicate_to_dfs_string in
      if restored = [] || List.exists (fun x -> repr x <> repr pc) restored
         || repr indexed <> repr pc then failwith "return guard lost in XML/dictionary round trip")
    [Eq; Ne; Lt; Le; Gt; Ge];
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PGuardedOutputs";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PGuardedOutputs" "guarded_outputs");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do ignore (CCHGenerateAndCheck.generate_and_check_process_file domains) done;
  let reads name =
    let selected = List.filter (fun po ->
        po#get_context#is_return_context && match po#get_predicate with
        | PInitialized (Mem _, _) -> name = "payload_bad"
        | PInitialized (Var ("p", _), _) -> name <> "payload_bad"
        | PInitialized (Var ("d", _), _) -> true
        | _ -> false) (proof_scaffolding#get_proof_obligations name) in
    if selected = [] then failwith (name ^ ": target return read missing"); selected in
  List.iter (fun name -> List.iter (fun po ->
      if not po#is_safe || po#is_violation then failwith (CU.located_po_to_string po);
      match po#get_dependencies with
      | Some (DEnvC (_, assumptions)) when List.exists (function
          | PostAssumption (_, XInitializedOnReturn _) -> true | _ -> false) assumptions -> ()
      | _ -> failwith (name ^ ": guard erased or proof became unconditional")) (reads name))
    ["success_good"; "saved_status_good"; "field_good"; "zero_good"; "negative_good";
     "direct_if_good"; "positive_good"; "nonpositive_good"; "nonzero_good";
     "constant_good"; "wider_status_good"; "struct_status_good"; "readonly_good";
     "both_framed_good"; "descriptor_good"; "checked_then_changed_good"];
  List.iter (fun name -> List.iter (fun po ->
      if po#is_safe then failwith (name ^ ": missing/wrong/stale guard or payload trusted")) (reads name))
    ["failure_bad"; "unguarded_bad"; "wrong_call_bad"; "overwritten_status_bad";
     "sibling_bad"; "zero_error_bad"; "narrow_status_unknown"; "opaque_bad";
     "different_call_bad"; "status_only_bad"; "normalized_error_bad"; "bool_status_bad";
     "signed_narrow_bad"; "unsigned_status_bad"; "masked_status_bad"; "arithmetic_status_bad";
     "partial_status_bad"; "union_status_bad"; "volatile_status_unknown"; "loop_status_unknown";
     "branch_gap_bad"; "payload_bad"; "descriptor_sibling_bad"; "nonzero_error_bad";
     "released_bad"; "narrow_field_bad"];
  CU.analysis_take_down "guarded_outputs";
  print_endline "guarded outputs: 16 conditional positives, 26 open controls, six comparison round trips passed"
