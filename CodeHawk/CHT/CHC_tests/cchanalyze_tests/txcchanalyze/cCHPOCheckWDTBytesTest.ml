(* Initialized-range byte bounds must retain every byte; typed index lengths
   retain their stride. Region/lifetime facts are deliberately not fabricated. *)
open CCHBasicTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils
let obligations name = proof_scaffolding#get_proof_obligations name
let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PWDTBytes";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PWDTBytes" "wdt_bytes");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain;
      sym_pointersets_domain] in
  for _round = 2 to 5 do
    ignore (CCHGenerateAndCheck.generate_and_check_process_file domains)
  done;
  List.iter (fun (name, good) ->
      let bounds = List.filter (fun po -> match po#get_predicate with
          | PPtrUpperBound _ -> true | _ -> false) (obligations name) in
      if bounds = [] then failwith (name ^ ": missing range bound");
      List.iter (fun po ->
          if good then (if not po#is_safe || po#is_violation then
              failwith (CU.located_po_to_string po))
          else if not po#is_violation then
              failwith (name ^ ": short source accepted")) bounds)
    ["bytes_good", true; "raw_bytes_good", true; "indices_good", true;
     "bytes_short_bad", false; "raw_bytes_short_bad", false;
     "indices_short_bad", false];
  let reads name =
    let rs = List.filter (fun po -> match po#get_predicate with
        | PInitialized (Var ("value", _), _) -> true | _ -> false)
        (obligations name) in
    if rs = [] then failwith (name ^ ": missing copied value read"); rs in
  List.iter (fun name -> List.iter (fun po ->
      if not po#is_safe || po#is_violation then
        failwith (CU.located_po_to_string po)) (reads name))
    ["scalar_good"; "union_good"; "field_good"; "last_good"; "readonly_good"];
  List.iter (fun po -> match po#get_dependencies with
      | Some (DEnvC (_, assumptions)) when assumptions <> [] -> ()
      | _ -> failwith "readonly frame dependency missing") (reads "readonly_good");
  List.iter (fun name -> List.iter (fun po ->
      if po#is_safe then failwith (name ^ ": region bytes/lifetime invented"))
      (reads name))
    ["partial_bad"; "sibling_bad"; "overwritten_bad"; "opaque_bad";
     "entry_unknown"; "loop_unknown"; "cleared_unknown";
     "allocated_unknown"; "acquired_unknown"; "failed_acquire_bad";
     "released_bad"];
  CU.analysis_take_down "wdt_bytes";
  print_endline "WDT byte controls: exact byte/index bounds and conservative regions passed"
