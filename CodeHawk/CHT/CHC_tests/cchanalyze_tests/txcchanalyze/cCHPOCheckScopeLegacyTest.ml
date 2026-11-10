(* Missing parser metadata is not evidence of function-block lifetime. *)
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils
let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PScopePermissions";
  ignore (CU.analysis_setup "PScopePermissionsLegacy" "scope_legacy");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do ignore (CCHGenerateAndCheck.generate_and_check_process_file domains) done;
  let checks name =
    let xs = List.filter (fun po -> match po#get_predicate with
        | PValidMem _ | PInScope _ -> true | _ -> false)
        (proof_scaffolding#get_proof_obligations name) in
    if xs = [] then failwith (name ^ ": missing lifetime obligations"); xs in
  List.iter (fun name -> List.iter (fun po ->
      if po#is_safe then failwith (name ^ ": missing parser certificate trusted"))
      (checks name)) ["live_local_read"; "live_local_write"];
  List.iter (fun name -> List.iter (fun po ->
      if not po#is_safe || po#is_violation then failwith (CU.located_po_to_string po))
      (checks name)) ["live_global_write"; "live_nested_static_write"];
  CU.analysis_take_down "scope_legacy";
  print_endline "legacy scope: automatic lifetime unknown; static/global storage retained"
