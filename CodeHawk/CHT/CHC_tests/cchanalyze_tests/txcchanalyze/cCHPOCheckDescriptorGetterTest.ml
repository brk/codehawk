(* Pointer-field getter summaries retain exact aliases and dependencies. *)
open CCHBasicTypes
open CCHPreTypes
open CCHLibTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils
let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PDescriptorGetter";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PDescriptorGetter" "descriptor_getter");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do ignore (CCHGenerateAndCheck.generate_and_check_process_file domains) done;
  let reads name =
    let result = List.filter (fun po -> match po#get_predicate with
        | PInitialized (Var ("value", _), _) -> true | _ -> false)
        (proof_scaffolding#get_proof_obligations name) in
    if result = [] then failwith (name ^ ": missing copied read"); result in
  let conditional po =
    if not po#is_safe || po#is_violation then failwith (CU.located_po_to_string po);
    match po#get_dependencies with
    | Some (DEnvC (_, assumptions)) when
        List.exists (function PostAssumption (_, XPreservesAllMemory) -> true | _ -> false) assumptions
        && List.exists (function
            | PostAssumption (_, XRelationalExpr (Eq, ReturnValue, ArgAddressedValue _)) -> true
            | _ -> false) assumptions -> ()
    | _ -> failwith "getter alias/frame dependency omitted" in
  List.iter (fun name -> List.iter conditional (reads name))
    ["getter_clear_good"; "getter_source_good"; "changed_descriptor_good"];
  List.iter (fun name -> List.iter (fun po ->
      if po#is_safe then failwith (name ^ ": unsafe/unsupported copied read proved")) (reads name))
    ["short_clear_bad"; "uncleared_bad"; "missing_metadata_bad"; "wrong_image_bad";
     "unmodeled_unknown"; "opaque_bad"; "released_bad"; "partial_metadata_bad";
     "root_escape_bad"; "post_only_unknown"; "opaque_metadata_bad";
     "readonly_escape_unknown"; "union_metadata_unknown"; "nested_descriptor_unknown";
     "ended_image_bad"; "freed_reclear_bad"];
  let pointerchecks = List.filter (fun po -> match po#get_predicate with
      | PNotNull (Lval (Var ("p", _), NoOffset)) -> true | _ -> false)
      (proof_scaffolding#get_proof_obligations "getter_clear_good") in
  if pointerchecks = [] then failwith "missing pointer check";
  List.iter conditional pointerchecks;
  let entries = List.filter (fun po -> match po#get_predicate with
      | PInitialized (_, Field (("pointer", _), NoOffset)) -> true
      | _ -> false) (proof_scaffolding#get_proof_obligations "missing_metadata_bad") in
  if entries = [] || List.exists (fun po -> po#is_safe) entries then
    failwith "getter postcondition supplied its own missing entry metadata";
  List.iter (fun po -> if not po#is_safe || po#is_violation then
      failwith "direct local control regressed") (reads "direct_good");
  CU.analysis_take_down "descriptor_getter";
  print_endline "descriptor getters: aliases conditional; escaped/partial/union/lifetime controls open"
