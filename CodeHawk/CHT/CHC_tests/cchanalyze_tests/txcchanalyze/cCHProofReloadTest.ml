(* A snapshot reload replaces managers instead of appending stale proof records. *)
open CCHProofScaffolding
module CU = TCHCchanalyzeUtils

let () =
  CCHSettings.system_settings#set_wordsize 64;
  CCHSettings.system_settings#set_undefined_behavior_analysis;
  CCHSettings.system_settings#set_contractpath "testinputs/PEntryPrefixFrame";
  ignore (CU.analysis_setup
      ~summaries_jar:(Some "testinputs/PErrnoWritten/cchsummaries.jar")
      "PEntryPrefixFrame" "copy_prefix_frame");
  let ppos = proof_scaffolding#get_ppo_manager "pure_copy" in
  let original = List.length ppos#get_ppos in
  let states () = List.sort compare (List.map (fun po -> po#index, po#get_status) ppos#get_ppos) in
  let original_states = states () in
  if original = 0 then failwith "reload: no primary obligations";
  let node = CHXmlDocument.xmlElement "ppos" in
  ppos#write_xml node;
  ppos#read_xml node;
  ppos#read_xml node;
  if List.length ppos#get_ppos <> original then
    failwith ("reload multiplied primary obligations: " ^ string_of_int original
      ^ " -> " ^ string_of_int (List.length ppos#get_ppos));
  if states () <> original_states then failwith "reload changed proof statuses";
  let duplicate = CHXmlDocument.xmlElement "ppos" in
  let first = List.hd (node#getTaggedChildren "ppo") in
  duplicate#appendChildren [first; first];
  let rejected = try ppos#read_xml duplicate; false with CCHUtilities.CCHFailure _ -> true in
  if not rejected then failwith "duplicate proof IDs were silently accepted";
  ppos#read_xml node;
  let spos = proof_scaffolding#get_spo_manager "event_before_copy" in
  let node = CHXmlDocument.xmlElement "spos" in
  spos#write_xml node;
  let original_count = List.length spos#get_spos in
  let original_calls = spos#get_callsite_manager#get_call_count in
  let original_returns = List.length ((node#getTaggedChild "returnsites")#getTaggedChildren "rs") in
  if original_count = 0 || original_calls = 0 || original_returns = 0 then
    failwith "reload: missing local/call/return controls";
  spos#read_xml node;
  spos#read_xml node;
  let result = CHXmlDocument.xmlElement "spos" in
  spos#write_xml result;
  if List.length spos#get_spos <> original_count
     || spos#get_callsite_manager#get_call_count <> original_calls
     || List.length ((result#getTaggedChild "returnsites")#getTaggedChildren "rs") <> original_returns then
    failwith "reload multiplied local requirements or call/return sites";
  let empty = CHXmlDocument.xmlElement "ppos" in
  ppos#read_xml empty;
  if ppos#get_ppos <> [] then failwith "empty snapshot retained stale primary obligations";
  CU.analysis_take_down "copy_prefix_frame";
  print_endline "proof reload: primary/local obligations and call/return sites remain unique"
