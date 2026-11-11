(* Inferred initialized input bytes remain exact API assumptions. *)
open CCHBasicTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils

let select name predicate =
  let found = List.filter (fun po -> predicate po#get_predicate)
      (proof_scaffolding#get_proof_obligations name) in
  if found = [] then failwith (name ^ ": missing requirement"); found

let is_range = function PInitializedRange _ -> true | _ -> false
let is_result = function PInitialized (Var ("result", _), NoOffset) -> true | _ -> false

let entry_bytes count po =
  match po#get_dependencies with
  | Some (DEnvC (_, [ApiAssumption (PInitializedRange
      (Lval (Var ("source", _), NoOffset), Const (CInt (n, _, _))))]))
       when po#is_safe && not po#is_violation && n = Int64.of_int count -> ()
  | _ -> failwith ("entry requirement: " ^ CU.located_po_to_string po)

let open_po po =
  if po#is_safe then failwith ("unsupported proof: " ^ CU.located_po_to_string po)

let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PParameterEntry";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PParameterEntry" "parameter_entry_requirement");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do
    ignore (CCHGenerateAndCheck.generate_and_check_process_file domains)
  done;
  List.iter (fun name ->
      List.iter (entry_bytes 4) (select name is_range);
      List.iter (entry_bytes 4) (select name is_result))
    ["scalar_copy"; "union_copy"; "read_before_event"; "before_switch";
     "formal_replaced_after"];
  List.iter (entry_bytes 4) (select "event_after_copy" is_range);
  List.iter open_po (select "event_after_copy" is_result);
  List.iter (entry_bytes 2) (select "short_copy" is_range);
  List.iter open_po (select "short_copy" is_result);
  List.iter (fun name -> List.iter open_po (select name is_range))
    ["event_before_copy"; "formal_replaced_before"; "lost_origin";
     "narrow_source"; "guarded_copy"; "nullable_copy"; "dirty_loop";
     "dirty_backedge"; "overwrite_before_copy"; "authored_short"];
  (* Project API propagation, including positive/negative caller SPOs, is
     checked separately by parameter_entry_followup.py. *)
  CU.analysis_take_down "parameter_entry_requirement";
  print_endline "parameter bytes: exact conditional prefixes, frames and caller propagation"
