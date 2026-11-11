(* An initialized entry range supplies only covered bytes within its frame. *)
open CCHBasicTypes
open CCHPreTypes
open CCHProofScaffolding

module CU = TCHCchanalyzeUtils

let run dir file check =
  CCHSettings.system_settings#set_contractpath ("testinputs/" ^ dir);
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar") dir file);
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do
    ignore (CCHGenerateAndCheck.generate_and_check_process_file domains)
  done;
  check ();
  CU.analysis_take_down file

let select name predicate =
  let chosen = List.filter (fun po -> predicate po#get_predicate)
      (proof_scaffolding#get_proof_obligations name) in
  if chosen = [] then failwith (name ^ ": missing obligation");
  chosen

let is_range = function PInitializedRange _ -> true | _ -> false

let is_copy_result = function
  | PInitialized (Var ("value", _), NoOffset) -> true
  | _ -> false

let expect pred po =
  if not (pred po) then failwith (CU.located_po_to_string po)

let entry_dependency po =
  match po#get_dependencies with
  | Some (DEnvC (_, deps)) when po#is_safe ->
     List.exists (function ApiAssumption (PInitializedRange _) -> true | _ -> false) deps
  | _ -> false

let positive name =
  List.iter (expect entry_dependency) (select name is_copy_result);
  List.iter (expect entry_dependency) (select name is_range)

let negative name =
  List.iter (expect (fun po -> not po#is_safe)) (select name is_range);
  List.iter (expect (fun po -> not (entry_dependency po))) (select name is_copy_result)

let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  run "PEntryInitializedImage" "entry_initialized_image" (fun () ->
      List.iter positive ["full_image"; "bounded_image"; "prefix_field"];
      List.iter negative ["short_image"; "unbounded_image"; "opaque_frame"; "write_frame";
                          "replaced_base"; "packed_image"; "loop_image"]);
  run "PPragmaEntryImage" "pragma_entry_image" (fun () -> negative "pragma_packed_image");
  print_endline "entry initialized images: three conditional proofs and open negative controls"
