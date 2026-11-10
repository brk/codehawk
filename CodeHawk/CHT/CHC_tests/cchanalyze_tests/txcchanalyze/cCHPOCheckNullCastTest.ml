(* Absolute-address rules must not discharge typed null pointers. *)
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils
let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PNullCast";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PNullCast" "null_cast");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do ignore (CCHGenerateAndCheck.generate_and_check_process_file domains) done;
  let checks name =
    let result = List.filter (fun po -> match po#get_predicate with
        | PNotNull _ -> true | _ -> false)
        (proof_scaffolding#get_proof_obligations name) in
    if result = [] then failwith (name ^ ": no nonnull check"); result in
  List.iter (fun name -> List.iter (fun po ->
      if not po#is_violation then failwith (name ^ ": null nonnull predicate not violated")) (checks name))
    ["null_direct_bad"; "null_void_bad"; "null_triple_bad"; "null_macro_bad";
     "dereference_direct_bad"; "dereference_void_bad"];
  List.iter (fun name -> List.iter (fun po ->
      if not po#is_safe || po#is_violation then failwith (name ^ ": address positive regressed")) (checks name))
    ["local_good"; "global_good"; "literal_good"; "cast_local_good"];
  CU.analysis_take_down "null_cast";
  print_endline "null casts: direct/nested/macros violate nonnull; actual addresses remain safe"
