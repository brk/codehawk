(* A copied local's call-entry bytes retain the original copy-site requirement. *)
open CCHBasicTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils

let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PCopyRangeFrame";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PCopyRangeFrame" "copy_range_frame");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do ignore (CCHGenerateAndCheck.generate_and_check_process_file domains) done;
  let query name =
    match List.filter (fun po -> match po#get_predicate with
        | PInitializedRange (AddrOf (Var ("value", _), NoOffset), _) -> true
        | _ -> false) (proof_scaffolding#get_proof_obligations name) with
    | [po] -> po
    | _ -> failwith (name ^ ": expected exactly one local range") in
  List.iter (fun (name, line) ->
      let result = query name in
      match result#get_dependencies with
      | Some (DReduced (_, [LocalAssumption (PInitializedRange _ as predicate)]))
           when result#is_safe ->
         let sources = List.filter (fun source -> source#get_predicate = predicate)
             (proof_scaffolding#get_spo_manager name)#get_spos in
         (match sources with
          | [source] when not source#is_safe && source#get_location.line = line ->
             let ordinary = List.filter (fun po ->
                 po#get_predicate = predicate && po#get_location.line = line &&
                 po#get_context#get_cfg_context#index = source#get_context#get_cfg_context#index)
                 (proof_scaffolding#get_ppo_manager name)#get_ppos in
             if List.length ordinary <> 1 || List.exists (fun po -> po#is_safe) ordinary then
               failwith (name ^ ": ordinary source requirement lost or initialized")
          | _ -> failwith (name ^ ": expected one open requirement at the original copy"))
      | _ -> failwith (name ^ ": local range lacks conditional source dependency"))
    ["straight", 13; "clean_break", 20; "event_before_copy", 46;
     "returning_path", 93; "copy_in_branch", 100; "replaced_image", 108;
     "second_image", 118];
  List.iter (fun name ->
      if (query name)#is_safe then failwith (name ^ ": unsafe or unsupported frame accepted"))
    ["dirty_fallthrough"; "event_after_copy"; "escaped_before_copy";
     "short_copy"; "guarded_copy"; "dirty_overwrite"; "loop_copy";
     "goto_copy"; "asm_copy"; "nested_copy"; "captured_return"];
  CU.analysis_take_down "copy_range_frame";
  print_endline "copied local ranges: seven conditional, eleven open, original source contexts retained"
