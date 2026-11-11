(* A destination read may reduce to an exact source requirement at the copy. *)
open CCHBasicTypes
open CCHPreTypes
open CCHProofScaffolding

module CU = TCHCchanalyzeUtils

let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PMemcpyFieldRequirement" "memcpy_field_requirement");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do
    ignore (CCHGenerateAndCheck.generate_and_check_process_file domains)
  done;
  let reads name =
    let selected = List.filter (fun po -> match po#get_predicate with
        | PInitialized (Var ("result", _), _) -> true
        | _ -> false) (proof_scaffolding#get_proof_obligations name) in
    if selected = [] then failwith (name ^ ": destination read missing");
    selected in
  List.iter (fun (name, line) ->
      List.iter (CU.check_open_copy_source ~line name) (reads name))
    ["copy_field", 17; "copy_field_alias", 25];
  List.iter (fun name -> List.iter (fun po ->
      match po#get_dependencies with
      | Some (DEnvC (_, [ApiAssumption (PInitializedRange
          (Lval (Var ("source", _), NoOffset), Const (CInt (n, _, _))))]))
           when po#is_safe && n = 4L -> ()
      | _ -> failwith (name ^ ": missing exact conditional parameter byte requirement"))
      (reads name)) ["copy_scalar_parameter"; "copy_union_parameter"];
  List.iter (fun name ->
      if List.exists (fun po -> po#is_safe) (reads name) then
        failwith (name ^ ": unsupported copy was reduced or discharged"))
    ["short_copy"; "narrow_field"; "lost_origin"; "uninitialized_local";
     "short_parameter_copy"; "narrow_parameter_copy"; "replaced_parameter"];
  CU.analysis_take_down "memcpy_field_requirement";
  print_endline "memcpy sources: open field requirements and exact conditional parameter bytes"
