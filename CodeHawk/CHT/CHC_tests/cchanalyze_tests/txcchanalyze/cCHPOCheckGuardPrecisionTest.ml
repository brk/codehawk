(* Terminal error conversions cannot taint a disjoint success continuation. *)
open CCHBasicTypes
open CCHLibTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils
let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PGuardPrecision";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PGuardPrecision" "guard_precision");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do ignore (CCHGenerateAndCheck.generate_and_check_process_file domains) done;
  let reads name =
    let selected = List.filter (fun po -> po#get_context#is_return_context &&
        match po#get_predicate with PInitialized (Var ("p", _), _) -> true | _ -> false)
        (proof_scaffolding#get_proof_obligations name) in
    if selected = [] then failwith (name ^ ": target read missing"); selected in
  List.iter (fun name -> List.iter (fun po ->
      if not po#is_safe || po#is_violation then failwith (CU.located_po_to_string po);
      match po#get_dependencies with
      | Some (DEnvC (_, assumptions)) when List.exists (function
          | PostAssumption (_, XInitializedOnReturn _) -> true | _ -> false) assumptions -> ()
      | _ -> failwith (name ^ ": return condition lost")) (reads name))
    ["guard_no_log_good"; "guard_error_log_wide_good"; "guard_error_log_narrow_good"];
  List.iter (fun name -> List.iter (fun po ->
      if po#is_safe then failwith (name ^ ": unsafe predecessor accepted")) (reads name))
    ["guard_cast_prefix_unknown"; "guard_cast_rejoin_unknown"; "guard_normalized_error_bad"];
  CU.analysis_take_down "guard_precision";
  print_endline "guard precision: three conditional positives and three open controls passed"
