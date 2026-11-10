(* A source-checked setter initializes descriptor fields without writing payload. *)
open CCHBasicTypes
open CCHLibTypes
open CCHPreTypes
open CCHProofScaffolding

module CU = TCHCchanalyzeUtils

let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PLocalSetters";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PLocalSetters" "local_setters");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do
    ignore (CCHGenerateAndCheck.generate_and_check_process_file domains)
  done;
  let reads name =
    let selected = List.filter (fun po -> match po#get_predicate with
        | PInitializedRange _ | PInitialized (Var ("value", _), _) -> true
        | _ -> false) (proof_scaffolding#get_proof_obligations name) in
    if selected = [] then failwith (name ^ ": initialized read missing");
    selected in
  let conditional po =
    match po#get_dependencies with
    | Some (DEnvC (invariants, assumptions)) when po#is_safe && not po#is_violation
          && invariants <> []
          && List.exists (function PostAssumption (_, XBufferOnReturn _) -> true | _ -> false)
               assumptions
          && List.exists (function PostAssumption (_, XPreservesAllMemory) -> true | _ -> false)
               assumptions -> ()
    | _ -> failwith (CU.located_po_to_string po) in
  List.iter (fun name -> List.iter conditional (reads name))
    ["exact_extent"; "copy_after_setter"];
  List.iter (fun name ->
      if List.exists (fun po -> po#is_safe) (reads name) then
        failwith (name ^ ": unsafe or unsupported initialized read accepted"))
    ["no_clear"; "cleared_logical_length"; "escaped_after_setter"; "narrow_capacity";
     "external_effect"; "opaque_effect"; "released_region"; "second_region_without_clear"];
  CU.analysis_take_down "local_setters";
  print_endline "local setters: two conditional consumers and eight open controls"
