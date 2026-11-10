(* Global no-free can preserve an origin, but cannot create one. *)
open CCHLibTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils
let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PNoFreeValidity";
  ignore (CU.analysis_setup
    ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
    "PNoFreeValidity" "nofree_validity");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
    valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do ignore (CCHGenerateAndCheck.generate_and_check_process_file domains) done;
  let checks name =
    let xs = List.filter (fun po -> match po#get_predicate with
      | PValidMem _ -> true | _ -> false)
      (proof_scaffolding#get_proof_obligations name) in
    if xs = [] then failwith (name ^ ": missing valid-memory check"); xs in
  List.iter (fun name -> List.iter (fun po -> if po#is_safe then
    failwith (CU.located_po_to_string po)) (checks name))
    ["nofree_opaque"; "nofree_absolute"];
  List.iter (fun name -> List.iter (fun po -> match po#get_dependencies with
    | Some (DEnvC (_, assumptions)) when po#is_safe &&
        List.exists (function GlobalAssumption XPreservesAllMemory -> true | _ -> false) assumptions &&
        List.exists (function ApiAssumption (PValidMem _) | PostAssumption (_, XValidMem ReturnValue) -> true
          | _ -> false) assumptions -> ()
    | _ -> failwith (name ^ ": initial validity or no-free premise omitted")) (checks name))
    ["nofree_valid"; "nofree_argument"];
  List.iter (fun po -> if not po#is_safe || po#is_violation then
    failwith (CU.located_po_to_string po)) (checks "nofree_local");
  CU.analysis_take_down "nofree_validity";
  print_endline "no-free: frame premise retains independent origin requirements"
