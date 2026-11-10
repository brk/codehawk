(* A preserved pointer needs explicit validity at its origin. *)
open CCHLibTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils
let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PReturnValidity";
  ignore (CU.analysis_setup
    ~summaries_jar:(Some "testinputs/PReturnValidity/cchsummaries.jar")
    "PReturnValidity" "return_validity");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
    valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do ignore (CCHGenerateAndCheck.generate_and_check_process_file domains) done;
  let checks name =
    let xs = List.filter (fun po -> match po#get_predicate with
      | PValidMem _ -> true | _ -> false)
      (proof_scaffolding#get_proof_obligations name) in
    if xs = [] then failwith (name ^ ": missing valid-memory check"); xs in
  let conditional po = match po#get_dependencies with
    | Some (DEnvC (_, assumptions)) when po#is_safe && not po#is_violation -> assumptions
    | _ -> failwith (CU.located_po_to_string po) in
  List.iter (fun name -> List.iter (fun po -> if po#is_safe then
    failwith (name ^ ": unsupported origin proved valid")) (checks name))
    ["opaque_use"; "opaque_readonly"; "integer_pointer"; "integer_return_use";
     "valid_opaque"; "error_use"; "new_only_use"; "heap_only_use"; "argument_opaque";
     "argument_bad_caller"];
  List.iter (fun name -> List.iter (fun po ->
    let assumptions = conditional po in
    if not (List.exists (function PostAssumption (_, XValidMem ReturnValue) -> true
      | _ -> false) assumptions) then failwith "return validity premise omitted") (checks name))
    ["valid_use"; "valid_readonly"; "nullable_use"];
  List.iter (fun name -> List.iter (fun po ->
    let assumptions = conditional po in
    List.iter (fun pred -> if not (List.exists (function PostAssumption (_, p) -> p = pred
      | _ -> false) assumptions) then failwith "allocation premise omitted")
      [XNewMemory ReturnValue; XHeapAddress ReturnValue]) (checks name))
    ["new_use"; "malloc_use"];
  List.iter (fun po -> let assumptions = conditional po in
    if not (List.exists (function PostAssumption (_, XNull ReturnValue) -> true
      | _ -> false) assumptions) then failwith "null error alternative omitted") (checks "nullable_use");
  List.iter (fun name -> List.iter (fun po -> let assumptions = conditional po in
    if not (List.exists (function ApiAssumption (PValidMem _) -> true | _ -> false) assumptions)
      then failwith "entry validity premise omitted") (checks name))
    ["argument_use"; "argument_readonly"];
  List.iter (fun name -> List.iter (fun po -> if not po#is_safe || po#is_violation then
    failwith (CU.located_po_to_string po)) (checks name))
    ["local_use"; "global_use"; "argument_good_caller"];
  (* A reduced primary result is not closure: free-exclusion supporting
     obligations must remain open for the same pointer after free. *)
  List.iter (fun name ->
    let xs = List.filter (fun po -> match po#get_predicate with
      | PDistinctRegion _ -> true | _ -> false)
      (proof_scaffolding#get_proof_obligations name) in
    if xs = [] || List.exists (fun po -> po#is_safe) xs then
      failwith (name ^ ": released-pointer support incorrectly closed"))
    ["malloc_freed"; "argument_freed"];
  CU.analysis_take_down "return_validity";
  print_endline "validity origins: returns/entry explicit; error/lifetime dependencies retained"
