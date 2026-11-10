(* Numeric addresses alone establish neither live objects nor their bounds. *)
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils
let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PAbsoluteValidity";
  ignore (CU.analysis_setup
    ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
    "PAbsoluteValidity" "absolute_validity");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
    valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do ignore (CCHGenerateAndCheck.generate_and_check_process_file domains) done;
  let checks name = List.filter (fun po -> match po#get_predicate with
    | PValidMem _ | PInScope _ | PLowerBound _ | PUpperBound _ -> true
    | _ -> false) (proof_scaffolding#get_proof_obligations name) in
  List.iter (fun name ->
    let xs = checks name in
    List.iter (fun pred -> if not (List.exists (fun po -> pred po#get_predicate) xs)
      then failwith (name ^ ": missing object check"))
      [(function PValidMem _ -> true | _ -> false);
       (function PInScope _ -> true | _ -> false);
       (function PLowerBound _ -> true | _ -> false);
       (function PUpperBound _ -> true | _ -> false)];
    List.iter (fun po -> if po#is_safe then failwith (CU.located_po_to_string po)) xs)
    ["absolute_direct"; "absolute_member"; "absolute_negative"];
  List.iter (fun name ->
    let xs = checks name in
    if xs = [] then failwith (name ^ ": no object check");
    List.iter (fun po -> if not po#is_safe || po#is_violation then
      failwith (CU.located_po_to_string po)) xs)
    ["local_address"; "global_address"; "literal_address"];
  let nullchecks = List.filter (fun po -> match po#get_predicate with
    | PNotNull _ -> true | _ -> false)
    (proof_scaffolding#get_proof_obligations "absolute_zero") in
  if nullchecks = [] || not (List.for_all (fun po -> po#is_violation) nullchecks)
    then failwith "null dereference lost its nonnull violation";
  CU.analysis_take_down "absolute_validity";
  print_endline "absolute addresses: object permissions remain open; real addresses retained"
