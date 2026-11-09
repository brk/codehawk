(* Opaque calls must invalidate numeric memory facts as well as symbolic
   initialization facts. Unsafe fixture functions are analyzed only. *)
open CCHBasicTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils

let obligations name = proof_scaffolding#get_proof_obligations name
let reads name variable =
  let rs = List.filter (fun po -> match po#get_predicate with
      | PInitialized (Var (v, _), _) -> v = variable
      | _ -> false) (obligations name) in
  if rs = [] then failwith (name ^ ": missing read of " ^ variable);
  rs

let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PServiceOutputs";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PServiceOutputs" "service_outputs");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain;
      sym_pointersets_domain] in
  for _round = 2 to 5 do
    ignore (CCHGenerateAndCheck.generate_and_check_process_file domains)
  done;
  List.iter (fun (name, variable) ->
      List.iter (fun po ->
          if not po#is_safe || po#is_violation then
            failwith (CU.located_po_to_string po);
          match po#get_dependencies with
          | Some (DEnvC (_, assumptions)) when assumptions <> [] -> ()
          | _ -> failwith (name ^ ": lost model dependency"))
        (reads name variable))
    ["direct_good", "index"; "loop_good", "index";
     "loop_reset_good", "depth"; "receive_good", "ptr";
     "receive_failure_good", "ptr"; "runloop_good", "status";
     "receive_staged_good", "ptr"; "runloop_staged_good", "status";
     "copy_then_readonly_good", "value"];
  List.iter (fun (name, variable) ->
      List.iter (fun po ->
          if po#is_safe then failwith (name ^ ": stale initialization survived"))
        (reads name variable))
    ["loop_stale_unknown", "index"; "loop_stale_unknown", "depth";
     "receive_perf_unknown", "ptr"; "runloop_perf_unknown", "status";
     "escaped_overwrite_bad", "index"; "copy_then_unknown_bad", "value";
     "copy_then_indirect_bad", "value"; "copy_then_postonly_bad", "value";
     "stale_bound_bad", "value"];
  List.iter (fun (name, variable) ->
      let rs = List.filter (fun po -> match po#get_predicate with
          | PIndexUpperBound (Lval (Var (v, _), NoOffset), _) -> v = variable
          | _ -> false) (obligations name) in
      if rs = [] || List.exists (fun po -> po#is_safe) rs then
        failwith (name ^ ": stale numeric bound survived"))
    ["stale_bound_bad", "value"; "indirect_return_bound_bad", "index"];
  CU.analysis_take_down "service_outputs";
  print_endline "service outputs: conservative call havoc and scoped outputs passed"
