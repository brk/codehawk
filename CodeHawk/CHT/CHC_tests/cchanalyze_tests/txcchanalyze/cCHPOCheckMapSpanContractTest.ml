(* Regenerate the production byte-loop controls from parser inputs. Supporting
   map/span requirements are additionally checked by frontend integration. *)
open CCHBasicTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils

let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PLCMapSpans";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PLCMapSpans" "lc_map_spans");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain;
      sym_pointersets_domain] in
  for _round = 2 to 5 do
    ignore (CCHGenerateAndCheck.generate_and_check_process_file domains)
  done;
  List.iter (fun name ->
      let reads = List.filter (fun po -> match po#get_predicate with
          | PInitialized (Var ("dest", _), _) -> true | _ -> false)
          (proof_scaffolding#get_proof_obligations name) in
      if reads = [] then failwith (name ^ ": missing destination read");
      List.iter (fun po ->
          if not po#is_safe || po#is_violation then
            failwith (CU.located_po_to_string po);
          match po#get_dependencies with
          | Some (DEnvC (_, assumptions)) when assumptions <> [] -> ()
          | _ -> failwith (name ^ ": missing contract dependency")) reads)
    ["map_two_bytes_good"; "map_four_bytes_good"; "map_first_index_bad";
     "map_second_index_bad"; "map_truncated_source_bad";
     "map_uninitialized_source_bad"; "map_missing_tail_bad";
     "map_changed_bad"; "map_wrapped_byte_bad"; "map_framed_good"];
  CU.analysis_take_down "lc_map_spans";
  print_endline "map spans: conditional field outputs retained for frontend entry checks"
