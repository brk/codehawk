(* A table acquisition initializes its output pointer value only. The model
   has no complete write footprint and grants no pointee or lifetime facts. *)
open CCHBasicTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils

let obligations name = proof_scaffolding#get_proof_obligations name

let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PTableAcquisition";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PTableAcquisition" "table_acquisition");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain;
      sym_pointersets_domain] in
  for _round = 2 to 5 do
    ignore (CCHGenerateAndCheck.generate_and_check_process_file domains)
  done;
  List.iter (fun name ->
      let reads = List.filter (fun po -> match po#get_predicate with
          | PInitialized (Var _, _) -> true | _ -> false) (obligations name) in
      if reads = [] then failwith (name ^ ": missing pointer value read");
      List.iter (fun po ->
          if not po#is_safe || po#is_violation then failwith (CU.located_po_to_string po);
          match po#get_dependencies with
          | Some (DEnvC (_, assumptions)) when assumptions <> [] -> ()
          | _ -> failwith (name ^ ": missing output postcondition dependency")) reads;
      let bounds = List.filter (fun po -> match po#get_predicate with
          | PPtrUpperBound _ -> true | _ -> false) (obligations name) in
      if bounds = [] || List.exists (fun po -> not po#is_safe || po#is_violation) bounds then
        failwith (name ^ ": byte-sized output slot was not accepted"))
    ["slot_good"; "field_slot_good"; "cast_slot_good"; "failure_slot_good"];
  List.iter (fun (name, expected) ->
      let bounds = List.filter (fun po -> match po#get_predicate with
          | PPtrUpperBound _ -> true | _ -> false) (obligations name) in
      if bounds = [] || List.exists (fun po ->
          if expected then not po#is_safe || po#is_violation else not po#is_violation) bounds then
        failwith (name ^ ": byte/index-size buffer interpretation changed"))
    ["explicit_bytes_good", true; "explicit_bytes_bad", false;
     "explicit_indices_good", true; "explicit_indices_bad", false;
     "slot_too_small_bad", false];
  List.iter (fun name ->
      if not (List.exists (fun po -> match po#get_predicate with
          | PPtrUpperBound _ | PPtrUpperBoundDeref _ -> po#is_violation | _ -> false) (obligations name)) then
        failwith (name ^ ": cast/address stride was counted in array elements"))
    ["larger_stride_bad"; "array_address_bad"];
  List.iter (fun name ->
      let unsafe = List.filter (fun po -> match po#get_predicate with
          | PInitialized _ | PInitializedRange _ -> not po#is_safe
          | _ -> false) (obligations name) in
      if unsafe = [] then failwith (name ^ ": unsafe target/frame became initialized"))
    ["sibling_slot_bad"; "pointee_bad"; "extent_bad"; "copy_pointee_bad";
     "released_bad"; "no_frame_bad"];
  CU.analysis_take_down "table_acquisition";
  print_endline "table acquisition: pointer-only postconditions, byte/index extents and unsafe targets/frames passed"
