(* Precision bounds narrow %s scans; width and negative precision do not. *)
open CCHBasicTypes
open CCHPreTypes
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils
let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PBoundedFormat";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PBoundedFormat" "bounded_format");
  let domains = CCHInvariantFact.[linear_equalities_domain; pepr_domain;
      valueset_domain; intervals_domain; symbolic_sets_domain; sym_pointersets_domain] in
  for _round = 2 to 5 do ignore (CCHGenerateAndCheck.generate_and_check_process_file domains) done;
  let rec source = function
    | StartOf (Var (("src" | "other"), _), _) -> true
    | CastE (_, e) | BinOp (PlusPI, e, _, _) -> source e
    | _ -> false in
  let pos name = proof_scaffolding#get_proof_obligations name in
  let ranges name = List.filter (fun po -> match po#get_predicate with
      | PInitializedRange (e, _) when source e -> true | _ -> false) (pos name) in
  List.iter (fun name ->
      let selected = List.filter (fun po -> match po#get_predicate with
          | PInitializedRange (e, _) | PNotNull e | PValidMem e
          | PPtrUpperBound (_, _, e, _) when source e -> true | _ -> false) (pos name) in
      if selected = [] || ranges name = [] then failwith (name ^ ": missing bounded scan");
      List.iter (fun po -> if not po#is_safe || po#is_violation then
          failwith (CU.located_po_to_string po)) selected;
      if List.exists (fun po -> match po#get_predicate with
          | PNullTerminated e when source e -> true | _ -> false) (pos name) then
        failwith (name ^ ": spurious NUL premise for bounded scan"))
    ["bounded_constant_good"; "bounded_argument_good"; "bounded_sizeof_good";
     "bounded_width_precision_good"; "bounded_multiple_good";
     "bounded_offset_good"; "zero_precision_good"];
  List.iter (fun name ->
      let selected = List.filter (fun po -> match po#get_predicate with
          | PNullTerminated e when source e -> true | _ -> false) (pos name) in
      if selected = [] || List.exists (fun po -> po#is_safe) selected then
        failwith (name ^ ": unbounded/wide scan requirement lost"))
    ["negative_precision_bad"; "unbounded_bad"; "fieldwidth_bad";
     "unknown_precision_unknown"; "wide_precision_unknown"; "terminated_good"];
  List.iter (fun name ->
      let selected = ranges name in
      if selected = [] || List.exists (fun po -> po#is_safe) selected then
        failwith (name ^ ": uninitialized prefix proved"))
    ["uninitialized_prefix_bad"; "partial_prefix_bad"];
  List.iter (fun name ->
      if not (List.exists (fun po -> match po#get_predicate with
          | PPtrUpperBound (_, _, e, _) when source e -> po#is_violation
          | _ -> false) (pos name)) then failwith (name ^ ": missing excessive scan bound"))
    ["excessive_precision_bad"; "excessive_offset_bad"];
  if not (List.exists (fun po -> match po#get_predicate with
      | PNotNull (CastE (_, Const (CInt (n, _, _)))) when n = 0L -> po#is_violation
      | _ -> false) (pos "zero_null_bad")) then
    failwith "zero precision incorrectly permitted null %s argument";
  CU.analysis_take_down "bounded_format";
  print_endline "bounded narrow printf: finite prefixes proved; unbounded/wide/partial controls retained"
