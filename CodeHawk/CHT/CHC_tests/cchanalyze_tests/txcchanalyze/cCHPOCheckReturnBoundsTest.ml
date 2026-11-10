(* Argument/return pointer values require an actual object lower-bound premise. *)
open CCHLibTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils
let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PReturnBounds";
  ignore (CU.analysis_setup ~summaries_jar:(Some "testinputs/PReturnBounds/cchsummaries.jar")
    "PReturnBounds" "return_bounds");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
    valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do ignore (CCHGenerateAndCheck.generate_and_check_process_file domains) done;
  let checks name =
    let xs = List.filter (fun po -> match po#get_predicate with
      | PLowerBound _ -> true | _ -> false)
      (proof_scaffolding#get_proof_obligations name) in
    if xs=[] then failwith (name ^ ": missing lower bound"); xs in
  List.iter (fun name -> List.iter (fun po -> if po#is_safe then
    failwith (name ^ ": unjustified object lower bound")) (checks name))
    ["opaque_bounds"; "valid_only_bounds"; "error_bounds"; "global_pointer_bounds"; "bad_caller_bounds"];
  List.iter (fun name -> List.iter (fun po -> match po#get_dependencies with
    | Some (DEnvC (_, assumptions)) when po#is_safe && not po#is_violation &&
        List.exists (function PostAssumption (_, XRevBuffer _) -> true | _ -> false) assumptions -> ()
    | _ -> failwith (CU.located_po_to_string po)) (checks name))
    ["modeled_bounds"; "nullable_bounds"; "malloc_bounds"];
  List.iter (fun po -> match po#get_dependencies with
    | Some (DEnvC (_, assumptions)) when po#is_safe &&
        List.exists (function ApiAssumption (PLowerBound _) -> true | _ -> false) assumptions -> ()
    | _ -> failwith "entry lower bound not delegated") (checks "entry_bounds");
  List.iter (fun name -> List.iter (fun po -> if not po#is_safe || po#is_violation then
    failwith (CU.located_po_to_string po)) (checks name))
    ["local_bounds"; "global_object_bounds"; "local_array_bounds"; "good_caller_bounds"];
  let negative=List.filter (fun po -> match po#get_predicate with
    | PPtrLowerBound _ -> true | _ -> false)
    (proof_scaffolding#get_proof_obligations "local_negative_bounds") in
  if negative=[] || not (List.for_all (fun po -> po#is_violation) negative) then
    failwith "negative offset from an actual array lost its violation";
  CU.analysis_take_down "return_bounds";
  print_endline "pointer lower bounds: origins explicit; real object and negative-offset controls retained"
