(* A call's initialized postcondition cannot satisfy its own entry condition. *)
open CCHBasicTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils

let obligations name = proof_scaffolding#get_proof_obligations name
let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PInitializedEntries";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PInitializedEntries" "service_entries");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain;
      sym_pointersets_domain] in
  for _round = 2 to 5 do
    ignore (CCHGenerateAndCheck.generate_and_check_process_file domains)
  done;
  List.iter (fun (name, good) ->
      let entries = List.filter (fun po -> match po#get_predicate with
          | PInitialized (Mem _, _) -> true | _ -> false) (obligations name) in
      if entries = [] then failwith (name ^ ": initialized entry was omitted");
      List.iter (fun po ->
          if po#is_safe <> good || po#is_violation then
            failwith (CU.located_po_to_string po)) entries;
      let outputs = List.filter (fun po -> match po#get_predicate with
          | PInitialized (Var _, _) -> true | _ -> false) (obligations name) in
      if outputs = [] then failwith (name ^ ": output read missing");
      List.iter (fun po ->
          if not po#is_safe then failwith (CU.located_po_to_string po);
          match po#get_dependencies with
          | Some (DEnvC (_, assumptions)) when assumptions <> [] -> ()
          | _ -> failwith (name ^ ": output lost its model dependency")) outputs)
    ["entry_good", true; "entry_bad", false; "field_good", true;
     "field_bad", false; "sibling_bad", false];
  CU.analysis_take_down "service_entries";
  print_endline "initialized entry: scalar/field requirements and negative callers passed"
