(* Metadata inspection only. summary_disk mirrors the pinned Coq 8.19.2+lsp
   library.ml, SHA256 8483e6e9295336f2085caf85c43ece5a219a1ebf964c1e81a40446e97913f135. *)
type summary_disk = {
  md_name : Names.DirPath.t;
  md_deps : (Names.DirPath.t * Safe_typing.vodigest) array;
  md_ocaml : string;
  md_info : Library_info.t list;
}

type inspected = {
  path : string;
  name : string;
  digest : Safe_typing.vodigest;
  deps : (Names.DirPath.t * Safe_typing.vodigest) array;
  json : Yojson.Basic.t;
}

let schema = "rocq.vo-inspection.v1"
let summary_id : summary_disk ObjFile.id = ObjFile.make_id "summary"
let library_id : Obj.t ObjFile.id = ObjFile.make_id "library"
let universes_id : (Univ.ContextSet.t * bool) option ObjFile.id = ObjFile.make_id "universes"

let string s = `String s
let hex d = string (Digest.to_hex d)
let digest_json = function
  | Safe_typing.Dvo_or_vi d -> `Assoc ["kind", string "Dvo_or_vi"; "library", hex d]
  | Safe_typing.Dvivo (d,u) ->
    `Assoc ["kind", string "Dvivo"; "library", hex d; "universes", hex u]

let verify_segment file (segment : 'a ObjFile.segment) =
  let channel = open_in_bin file in
  Fun.protect ~finally:(fun () -> close_in channel) (fun () ->
    let size = LargeFile.in_channel_length channel in
    if segment.pos < 16L || segment.len < 0L ||
       segment.len > Int64.of_int max_int ||
       segment.pos > size || Int64.add segment.len 16L > Int64.sub size segment.pos
    then failwith "A Coq segment leaves its bound object file.";
    LargeFile.seek_in channel segment.pos;
    let computed = Digest.channel channel (Int64.to_int segment.len) in
    let trailing = Digest.input channel in
    if computed <> segment.hash || trailing <> segment.hash
    then failwith "A Coq segment payload or trailing digest differs.";
    `Assoc ["name", string segment.name; "position", string (Int64.to_string segment.pos);
            "bytes", string (Int64.to_string segment.len); "MD5", hex computed])

let inspect file =
  let handle = ObjFile.open_in ~file in
  Fun.protect ~finally:(fun () -> ObjFile.close_in handle) (fun () ->
    let segments = CString.Map.bindings (ObjFile.segments handle) in
    let verified = List.map (fun (_, segment) -> verify_segment file segment) segments in
    let summary, _ = ObjFile.marshal_in_segment handle ~segment:summary_id in
    let library = ObjFile.get_segment handle ~segment:library_id in
    let universes, universes_hash = ObjFile.marshal_in_segment handle ~segment:universes_id in
    let digest = match universes with
      | Some (_, true) -> Safe_typing.Dvivo (library.hash, universes_hash)
      | None | Some (_, false) -> Safe_typing.Dvo_or_vi library.hash
    in
    let name = Names.DirPath.to_string summary.md_name in
    let imports = Array.to_list summary.md_deps |> List.map (fun (name, digest) ->
      `Assoc ["module", string (Names.DirPath.to_string name); "required", digest_json digest]) in
    let json = `Assoc ["path", string file; "module", string name;
                       "digest", digest_json digest; "imports", `List imports;
                       "verified_segments", `List verified] in
    {path=file; name; digest; deps=summary.md_deps; json})

let main () =
  if Coq_config.vo_version <> 81999l || Coq_config.version <> "8.19.2+lsp"
  then failwith "The Coq inspector toolchain or object schema differs.";
  let open Yojson.Basic.Util in
  let request = Yojson.Basic.from_channel stdin in
  if (request |> member "schema" |> to_string) <> "rocq.vo-inspection.request.v1"
  then failwith "The Coq inspection request schema differs.";
  let objects = request |> member "objects" |> to_list |> List.map to_string in
  let inspected = Hashtbl.create (List.length objects) in
  List.iter (fun file ->
    if Hashtbl.mem inspected file then failwith "The inspection repeats an object.";
    Hashtbl.add inspected file (inspect file)) objects;
  let checks = request |> member "checks" |> to_list |> List.map (fun check ->
    let owner_path = check |> member "owner" |> to_string in
    let dependency_path = check |> member "object" |> to_string in
    let module_name = check |> member "module" |> to_string in
    let owner = Hashtbl.find inspected owner_path in
    let dependency = Hashtbl.find inspected dependency_path in
    if dependency.name <> module_name then failwith "A resolved Coq object has another module name.";
    let required = Array.to_list owner.deps |> List.filter (fun (name, _) ->
      Names.DirPath.to_string name = module_name) in
    let required = match required with
      | [(_,digest)] -> digest
      | _ -> failwith "The Coq object lacks one exact recorded import."
    in
    let compatible = Safe_typing.digest_match ~actual:dependency.digest ~required in
    `Assoc ["owner", string owner.path; "module", string module_name;
            "object", string dependency.path; "required", digest_json required;
            "actual", digest_json dependency.digest; "compatible", `Bool compatible]) in
  `Assoc ["schema", string schema; "coq_version", string Coq_config.version;
          "vo_version", `Int (Int32.to_int Coq_config.vo_version);
          "objects", `List (List.map (fun path -> (Hashtbl.find inspected path).json) objects);
          "checks", `List checks]

let () =
  try
    let result = main () in
    Yojson.Basic.to_channel stdout result;
    output_char stdout '\n'
  with error ->
    prerr_endline (Printexc.to_string error);
    exit 2
