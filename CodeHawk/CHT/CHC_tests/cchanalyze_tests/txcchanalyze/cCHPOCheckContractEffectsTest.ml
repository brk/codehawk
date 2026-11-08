(* Regenerate invariants from parser inputs and explicit effect contracts.
   Unsafe C controls are never executed. *)
open CCHBasicTypes
open CCHPreTypes
open CCHProofScaffolding

module CU = TCHCchanalyzeUtils

let obligations name = proof_scaffolding#get_proof_obligations name

let initialized_read name variable =
  let selected = List.filter (fun po -> match po#get_predicate with
      | PInitialized (Var (v, _), _) -> v = variable
      | _ -> false) (obligations name) in
  if selected = [] then failwith (name ^ ": missing initialized read of " ^ variable);
  selected

let conditional name variable =
  List.iter (fun po ->
  if not po#is_safe || po#is_violation then failwith (CU.located_po_to_string po);
  match po#get_dependencies with
  | Some (DEnvC (_, assumptions)) when assumptions <> [] -> ()
  | _ -> failwith (name ^ ": modeled result lost its contract dependencies"))
    (initialized_read name variable)

let unresolved name variable =
  List.iter (fun po ->
      if po#is_safe then failwith (name ^ ": write incorrectly preserved initialization"))
    (initialized_read name variable)

let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PContractEffects";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PContractEffects" "contract_outputs");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain;
      sym_pointersets_domain] in
  for _round = 2 to 5 do
    ignore (CCHGenerateAndCheck.generate_and_check_process_file domains)
  done;
  conditional "initialized_output_good" "out";
  conditional "initialized_failure_good" "out";
  conditional "uninitialized_failure_bad" "out";
  conditional "frame_good" "keep";
  unresolved "block_write_invalidates_bad" "out";
  unresolved "missing_footprint_bad" "keep";
  conditional "union_field_good" "out";
  conditional "nested_field_good" "out";
  unresolved "union_wider_bad" "out";
  unresolved "nested_sibling_bad" "out";
  List.iter (fun (name, variable) ->
      let selected = List.filter (fun po -> match po#get_predicate with
          | PIndexUpperBound (Lval (Var (v, _), NoOffset), _) -> v = variable
          | _ -> false) (obligations name) in
      if selected = [] || List.exists (fun po -> po#is_safe) selected then
        failwith (name ^ ": a block write was dropped"))
    ["two_outputs_first_bad", "first"; "two_outputs_second_bad", "second"];
  CU.analysis_take_down "contract_outputs";
  print_endline "contract effects: conditional output/frame, unknown writers, and multiple writes passed"
