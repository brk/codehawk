(* Exact local aliases, typed byte offsets and conservative escaped-slot frames. *)
open CCHBasicTypes
open CCHPreTypes
open CCHLibTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils
let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PAliasBytes";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PAliasBytes" "alias_bytes");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do ignore (CCHGenerateAndCheck.generate_and_check_process_file domains) done;
  let reads name =
    let rs = List.filter (fun po -> match po#get_predicate with
        | PInitialized (Var ("value", _), _) -> true | _ -> false)
        (proof_scaffolding#get_proof_obligations name) in
    if rs = [] then failwith (name ^ ": copied read missing"); rs in
  List.iter (fun name -> List.iter (fun po ->
      if not po#is_safe || po#is_violation then failwith (CU.located_po_to_string po)) (reads name))
    ["pointer_seed_good"; "descriptor_seed_good"; "pointer_source_good";
     "descriptor_source_good"; "field_source_good"; "scalar_alias_good";
     "byte_offset_good"; "typed_offset_good"; "count_changed_good";
     "pointer_changed_good"; "captured_length_good"; "captured_source_good"];
  List.iter (fun name -> List.iter (fun po ->
      if not po#is_safe || po#is_violation then failwith (CU.located_po_to_string po);
      match po#get_dependencies with
      | Some (DEnvC (_, assumptions)) when assumptions <> [] -> ()
      | _ -> failwith (name ^ ": alias/frame model dependency omitted")) (reads name))
    ["readonly_good"; "model_alias_good"];
  List.iter (fun name -> List.iter (fun po ->
      if po#is_safe then failwith (name ^ ": stale/unsupported address or interval trusted")) (reads name))
    ["short_count_bad"; "oversized_count_bad"; "reassign_before_bad";
     "reassign_after_bad"; "descriptor_reassign_bad"; "wrong_stride_bad";
     "opaque_bad"; "alias_overwrite_bad"; "descriptor_overwrite_bad";
     "indirect_bad"; "released_bad"; "escaped_slot_unknown";
     "escaped_descriptor_unknown"; "partial_slot_unknown";
     "integer_cast_unknown"; "union_slot_unknown"; "ambiguous_unknown";
     "arithmetic_alias_unknown"; "external_unknown"; "allocation_unknown";
     "disjoint_alias_unknown"];
  List.iter (fun po -> match po#get_dependencies with
      | Some (DEnvC (_, assumptions)) when List.exists (function
          | PostAssumption (_, XRelationalExpr (Eq, ReturnValue, _)) -> true
          | _ -> false) assumptions -> ()
      | _ -> failwith "modeled identity lost return-alias dependency") (reads "model_alias_good");
  List.iter (fun name ->
      let ranges = List.filter (fun po -> match po#get_predicate with
          | PInitializedRange _ -> true | _ -> false)
          (proof_scaffolding#get_proof_obligations name) in
      if ranges = [] || List.exists (fun po -> not po#is_safe || po#is_violation) ranges then
        failwith (name ^ ": initialized source-range entry missing or open"))
    ["pointer_source_good"; "descriptor_source_good"; "field_source_good"; "captured_length_good"];
  CU.analysis_take_down "alias_bytes";
  print_endline "alias bytes: exact locals, descriptors, offsets, captured facts and invalidation passed"
