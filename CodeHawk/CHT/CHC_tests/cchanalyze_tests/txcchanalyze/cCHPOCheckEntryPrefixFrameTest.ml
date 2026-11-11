(* Explicit entry bytes are usable only on paths preserving them up to the use. *)
open CCHBasicTypes
open CCHPreTypes
open CCHProofScaffolding

module CU = TCHCchanalyzeUtils

let entry_dependency po =
  match po#get_dependencies with
  | Some (DEnvC (_, deps)) when po#is_safe ->
     List.exists (function ApiAssumption (PInitializedRange _) -> true | _ -> false) deps
  | _ -> false

let select name predicate =
  let selected = List.filter (fun po -> predicate po#get_predicate)
      (proof_scaffolding#get_proof_obligations name) in
  if selected = [] then failwith (name ^ ": missing primary requirement");
  selected

let is_range = function PInitializedRange _ -> true | _ -> false
let is_result = function PInitialized (Var ("result", _), NoOffset) -> true | _ -> false

let expect name check po =
  if not (check po) then failwith (name ^ ": " ^ CU.located_po_to_string po)

let run directory check =
  try
  CCHSettings.system_settings#set_contractpath ("testinputs/" ^ directory);
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      directory "copy_prefix_frame");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do
    ignore (CCHGenerateAndCheck.generate_and_check_process_file domains)
  done;
  check ();
  CU.analysis_take_down "copy_prefix_frame"
  with CHCommon.CHFailure p ->
    failwith (directory ^ ": " ^ CHPrettyUtil.pretty_to_string p)

let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  run "PEntryPrefixFrame" (fun () ->
      List.iter (fun name ->
          List.iter (expect name entry_dependency) (select name is_range);
          List.iter (expect name entry_dependency) (select name is_result))
        ["pure_copy"; "read_before_event"; "dirty_returning_path";
         "formal_replaced_after_copy"; "bounded_field_before_event"; "copy_before_switch"];
      List.iter (expect "event_after_copy" entry_dependency)
        (select "event_after_copy" is_range);
      (* Entry bytes do not preserve a copied local through a later opaque call. *)
      List.iter (expect "event_after_copy" (fun po -> not po#is_safe))
        (select "event_after_copy" is_result);
      List.iter (fun name ->
          List.iter (expect name (fun po -> not po#is_safe)) (select name is_range);
          List.iter (CU.check_open_copy_source name) (select name is_result))
        ["event_before_copy"; "dirty_joining_path"; "overwrite_source_before_copy";
         "asm_after_copy"; "formal_replaced_before_copy"; "bounded_field_after_event";
         "dirty_switch_before_copy"; "dirty_switch_fallthrough"];
      List.iter (fun name ->
          List.iter (expect name (fun po -> not po#is_safe)) (select name is_range);
          List.iter (expect name (fun po -> not po#is_safe)) (select name is_result))
        ["dirty_loop"; "dirty_backwards_goto"];
      (* External entry requirements are generated in the engine unit pass.
       * Defined-callee caller SPOs additionally use project API propagation;
       * those are checked by the standalone project replay. *)
      List.iter (expect "initialized_external_caller" (fun po -> po#is_safe))
        (select "initialized_external_caller" is_range);
      List.iter (expect "uninitialized_external_caller" (fun po -> not po#is_safe))
        (select "uninitialized_external_caller" is_range));
  print_endline "entry prefixes: exact call facts, dirty predecessors/backedges and missing certificates retained"
