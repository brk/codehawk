(* Global aliases select exact copy-site requirements, never initialized bytes. *)
open CCHBasicTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils

let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PGlobalFieldCopy";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PGlobalFieldCopy" "global_field_copy");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do ignore (CCHGenerateAndCheck.generate_and_check_process_file domains) done;
  let reads name =
    let found = List.filter (fun po -> match po#get_predicate with
        | PInitialized (Var ("result", _), _) -> true | _ -> false)
        (proof_scaffolding#get_proof_obligations name) in
    if found = [] then failwith (name ^ ": missing copied read"); found in
  List.iter (fun (name, line, count) ->
      let found = reads name in
      if List.length found <> count then failwith (name ^ ": copied read count "
          ^ string_of_int (List.length found) ^ ": "
          ^ String.concat "; " (List.map CU.located_po_to_string found));
      List.iter (CU.check_open_copy_source ~line name) found)
    ["comparison", 16, 6; "changed_global_before", 33, 1; "changed_global_after", 40, 1];
  List.iter (fun (variable, line) ->
      let found = List.filter (fun po -> match po#get_predicate with
          | PInitialized (Var (name, _), NoOffset) -> name = variable | _ -> false)
          (proof_scaffolding#get_proof_obligations "two_images") in
      if List.length found <> 1 then failwith (variable ^ ": missing image copy read");
      List.iter (CU.check_open_copy_source ~line "two_images") found)
    ["first", 97; "second", 100];
  List.iter (fun name ->
      let primary = List.filter (fun po -> match po#get_predicate with
          | PInitializedRange _ -> true | _ -> false)
          (proof_scaffolding#get_ppo_manager name)#get_ppos in
      let local = List.filter (fun po -> match po#get_predicate with
          | PInitializedRange _ -> true | _ -> false)
          (proof_scaffolding#get_spo_manager name)#get_spos in
      if List.length local <> (if name = "two_images" then 2 else 1) then
        failwith (name ^ ": source context count");
      List.iter (fun requirement ->
          if requirement#is_safe || not (List.exists (fun source ->
              source#get_predicate = requirement#get_predicate &&
              source#get_context#get_cfg_context#index = requirement#get_context#get_cfg_context#index) primary) then
            failwith (name ^ ": source requirement moved away from its library call")) local)
    ["comparison"; "changed_global_before"; "changed_global_after"; "two_images"];
  List.iter (fun name -> List.iter (fun po ->
      if po#is_safe then failwith (name ^ ": unsupported copied read")) (reads name))
    ["event_after_copy"; "short_copy"; "volatile_source"; "narrow_source";
     "packed_source"; "integer_address"];
  List.iter (fun name -> List.iter (fun po -> match po#get_predicate with
      | PInitializedRange _ when po#is_safe -> failwith (name ^ ": global bytes invented")
      | _ -> ()) (proof_scaffolding#get_proof_obligations name))
    ["comparison"; "changed_global_before"; "changed_global_after"];
  CU.analysis_take_down "global_field_copy";
  print_endline "global copies: ten conditional reads, five open copy-site byte requirements"
