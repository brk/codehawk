(* The LC byte loop's postcondition is conditional. Source, map and preserved
   destination bytes remain explicit entry requirements. Unsafe C is not run. *)
open CCHBasicTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils

let obligations name = proof_scaffolding#get_proof_obligations name

let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PLCByteCopy";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PLCByteCopy" "lc_copy_model");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain;
      sym_pointersets_domain] in
  for _round = 2 to 5 do
    ignore (CCHGenerateAndCheck.generate_and_check_process_file domains)
  done;
  List.iter (fun name ->
      let reads = List.filter (fun po -> match po#get_predicate with
          | PInitialized (Var ("dest", _), _) -> true | _ -> false)
          (obligations name) in
      if reads = [] then failwith (name ^ ": missing destination read");
      List.iter (fun po ->
          if not po#is_safe || po#is_violation then
            failwith (CU.located_po_to_string po);
          match po#get_dependencies with
          | Some (DEnvC (_, assumptions)) when assumptions <> [] -> ()
          | _ -> failwith (name ^ ": missing postcondition dependency")) reads)
    ["swap_full_good"; "swap_partial_good";
     "swap_truncated_bad"; "swap_uninitialized_source_bad";
     "swap_partial_source_bad"; "swap_uninitialized_map_bad";
     "swap_uninitialized_tail_bad"; "swap_oversized_bad"];
  let fdecls = (CCHPreFileIO.read_function_semantics "swap_full_good").sdecls in
  let query = object method fenv = fdecls end in
  let zero = CHNumerical.numerical_zero in
  let indexzero = CCHLibTypes.ArgIndexOffset (zero, CCHLibTypes.ArgNoOffset) in
  let array = TArray (TInt (IUChar, []), Some (Const (CInt (4L, IInt, None))), []) in
  (match CCHPOPredicate.s_offset_to_offset array indexzero with
   | Ok (Index (Const (CInt (0L, _, _)), NoOffset)) -> ()
   | _ -> failwith "contract array index zero was dropped");
  (match CCHPOPredicate.s_offset_to_offset (TInt (IUChar, [])) indexzero with
   | Ok NoOffset -> ()
   | _ -> failwith "scalar addressed index zero changed meaning");
  List.iter (fun (typ, value, expected) ->
      let exp = CastE (typ, Const (CInt (Int64.of_int value, IInt, None))) in
      let result = CCHMemoryInitialization.literal_value query exp in
      let actual = match result with
        | Some x -> (match CCHMemoryInitialization.constant x with
            | Some n -> n#equal (CHNumerical.mkNumerical value)
            | _ -> false)
        | _ -> false in
      if actual <> expected then failwith "constant extent cast was misinterpreted")
    [TInt (IUInt, []), 4, true;
     TInt (IUChar, []), 255, true;
     TInt (IUChar, []), 260, false;
     TInt (ISChar, []), 255, false;
     TInt (IBool, []), 2, false;
     TPtr (TInt (IInt, []), []), 4, false];
  CU.analysis_take_down "lc_copy_model";
  print_endline "byte-copy contract: conditional fields and bounded extent casts passed"
