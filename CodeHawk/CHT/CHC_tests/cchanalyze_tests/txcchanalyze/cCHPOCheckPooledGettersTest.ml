(* Scope-certified local descriptors exposed only to exact read-only getters. *)
open CCHLibTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils
let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PPooledGetters";
  ignore (CU.analysis_setup ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
    "PPooledGetters" "pooled_getters");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do ignore (CCHGenerateAndCheck.generate_and_check_process_file domains) done;
  let reads name =
    let xs = List.filter (fun po -> match po#get_predicate with
        | PInitialized (CCHBasicTypes.Var ("value", _), _) -> true | _ -> false)
        (proof_scaffolding#get_proof_obligations name) in
    if xs = [] then failwith (name ^ ": missing copied read"); xs in
  List.iter (fun name -> List.iter (fun po -> match po#get_dependencies with
      | Some (DEnvC (_, assumptions)) when po#is_safe && not po#is_violation
          && List.exists (function PostAssumption (_, XBufferOnReturn _) -> true | _ -> false) assumptions
          && List.exists (function PostAssumption (_, XRelationalExpr _) -> true | _ -> false) assumptions
          && List.exists (function PostAssumption (_, XPreservesAllMemory) -> true | _ -> false) assumptions -> ()
      | _ -> failwith (CU.located_po_to_string po)) (reads name))
    ["two_getters_good"; "pointer_getter_good"; "size_getter_good";
     "captured_getters_good"; "field_getters_good"];
  List.iter (fun name -> List.iter (fun po -> if po#is_safe then
      failwith (name ^ ": unsafe or unsupported copied read closed")) (reads name))
    ["zero_getter_bad"; "partial_getter_bad"; "oversized_getter_bad";
     "released_getter_bad"; "opaque_getter_bad"; "escaped_getter_unknown";
     "missing_getter_bad"; "nested_getter_unknown"; "unguarded_getter_bad";
     "field_partial_bad"];
  CU.analysis_take_down "pooled_getters";
  print_endline "pooled getters: five conditional reads; ten unsafe/unsupported reads open"
