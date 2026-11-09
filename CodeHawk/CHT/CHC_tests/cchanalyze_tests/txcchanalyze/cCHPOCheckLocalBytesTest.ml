(* Exact initialized bytes from lib:string memset, with conservative frames,
   subobjects, branch joins and lifetime/control-flow restrictions. *)
open CCHBasicTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils
let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PLocalBytes";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PLocalBytes" "local_bytes");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain;
      sym_pointersets_domain] in
  for _round = 2 to 5 do
    ignore (CCHGenerateAndCheck.generate_and_check_process_file domains)
  done;
  let reads name =
    let rs = List.filter (fun po -> match po#get_predicate with
        | PInitialized (Var ("value", _), _) -> true | _ -> false)
        (proof_scaffolding#get_proof_obligations name) in
    if rs = [] then failwith (name ^ ": copied read missing"); rs in
  List.iter (fun name -> List.iter (fun po ->
      if not po#is_safe || po#is_violation then
        failwith (CU.located_po_to_string po)) (reads name))
    ["full_array_good"; "full_scalar_good"; "full_union_good"; "field_good";
     "nested_good"; "partial_good"; "partial_typed_good"; "branches_good";
     "disjoint_write_good"; "disjoint_field_good"; "direct_clear_good"; "pointer_alias_unknown"; "descriptor_unknown"];
  List.iter (fun name -> List.iter (fun po ->
      if not po#is_safe || po#is_violation then
        failwith (CU.located_po_to_string po);
      match po#get_dependencies with
      | Some (DEnvC (_, assumptions)) when assumptions <> [] -> ()
      | _ -> failwith (name ^ ": frame dependency omitted")) (reads name))
    ["readonly_good"; "framed_other_good"];
  List.iter (fun name -> List.iter (fun po ->
      if po#is_safe then failwith (name ^ ": byte interval invented or survived write"))
      (reads name))
    ["partial_bad"; "hole_bad"; "sibling_bad"; "narrow_union_bad";
     "conditional_bad"; "branches_gap_bad"; "overwrite_bad";
     "field_overwrite_bad"; "direct_alias_bad"; "opaque_bad"; "post_only_bad";
     "indirect_bad"; "released_bad"; "beyond_bad"; "oversized_clear_bad";
     "volatile_unknown"; "user_clear_unknown"; "clear_indirect_unknown";
     "allocation_unknown"; "loop_lifetime_unknown"; "asm_unknown";
     "two_clears_unknown";
     "vla_unknown"; "direct_partial_bad"; "direct_model_bad";
     "direct_model_partial_bad"];
  CU.analysis_take_down "local_bytes";
  print_endline "local memset bytes: intervals, fields, joins, frames and invalidation passed"
