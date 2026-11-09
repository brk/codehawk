(* CIL-flattened lexical lifetimes must not become alias initialization facts. *)
open CCHBasicTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils
let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PLocalLifetime";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PLocalLifetime" "alias_lifetime");
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
    ["function_scope_good"; "top_branch_good"; "direct_nested_good"];
  List.iter (fun name -> List.iter (fun po ->
      if po#is_safe then failwith (name ^ ": flattened local lifetime trusted")) (reads name))
    ["ended_block_bad"; "ended_branch_bad"; "ended_compound_bad";
     "ended_statement_expr_bad"; "shadowed_bad";
     "live_nested_unknown"; "nested_slot_unknown"];
  CU.analysis_take_down "alias_lifetime";
  print_endline "local lifetime: function scopes prove; nested and ended aliases stay open"
