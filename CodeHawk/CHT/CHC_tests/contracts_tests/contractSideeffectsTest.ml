open CHXmlDocument
open CCHFileContract
open CCHLibTypes

let parameter () =
  let p = xmlElement "par" in
  p#setAttribute "name" "value";
  p#setIntAttribute "nr" 1;
  p

let function_node () =
  let f = xmlElement "function" in
  let pars = xmlElement "parameters" in
  let effects = xmlElement "sideeffects" in
  let effect = xmlElement "sideeffect" in
  let math = xmlElement "math" in
  let apply = xmlElement "apply" in
  f#setAttribute "name" "keep_allocation";
  pars#appendChildren [parameter ()];
  apply#appendChildren [xmlElement "preserves-all-memory"];
  math#appendChildren [apply];
  effect#appendChildren [math];
  effects#appendChildren [effect];
  f#appendChildren [pars; effects];
  f

let load f =
  let root = xmlElement "cfile" in
  let fs = xmlElement "functions" in
  root#setAttribute "name" "effect_fixture";
  fs#appendChildren [f];
  root#appendChildren [fs];
  file_contract#reset;
  file_contract#read_xml root;
  file_contract#get_function_contract "keep_allocation"

let check c =
  match c#get_sideeffects with
  | [XPreservesAllMemory] -> ()
  | _ -> failwith "allocation-lifetime side effect was dropped"

let () =
  let c = load (function_node ()) in
  check c;
  let serialized = xmlElement "function" in
  serialized#setAttribute "name" "keep_allocation";
  c#write_xmlx serialized;
  check (load serialized);
  print_endline "contract side-effect read/write/read: passed"
