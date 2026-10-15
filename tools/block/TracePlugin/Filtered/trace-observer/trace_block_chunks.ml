let physical_limit = 2 * 1024 * 1024
let payload_limit = 256 * 1024
let children_limit = 256

let checked_hash line =
  if String.length line < 64 then failwith "sha256sum returned a short hash";
  let hash = String.sub line 0 64 in
  String.iter (function '0'..'9' | 'a'..'f' -> () | _ ->
    failwith "sha256sum returned an invalid hash") hash;
  hash

let sha256_file path =
  let channel = Unix.open_process_args_in "sha256sum" [|"sha256sum"; "--binary"; path|] in
  let line = input_line channel in
  match Unix.close_process_in channel with
  | Unix.WEXITED 0 -> checked_hash line
  | _ -> failwith "sha256sum failed"

let sha256_text text =
  let read_input, write_input = Unix.pipe ~cloexec:true () in
  let read_output, write_output = Unix.pipe ~cloexec:true () in
  let pid = Unix.create_process "sha256sum" [|"sha256sum"; "--binary"|]
    read_input write_output Unix.stderr in
  Unix.close read_input; Unix.close write_output;
  let outgoing = Unix.out_channel_of_descr write_input in
  let incoming = Unix.in_channel_of_descr read_output in
  output_string outgoing text; close_out outgoing;
  let line = input_line incoming in
  close_in incoming;
  match snd (Unix.waitpid [] pid) with
  | Unix.WEXITED 0 -> checked_hash line
  | _ -> failwith "sha256sum failed on a text payload"

type reference = { path : string; sha256 : string; bytes : int; logical_bytes : int }
let reference_json reference = `Assoc [
  "path", `String reference.path; "sha256", `String reference.sha256;
  "bytes", `Int reference.bytes; "logical_bytes", `Int reference.logical_bytes]
let root_json reference = `Assoc [
  "path", `String reference.path; "sha256", `String reference.sha256;
  "bytes", `Int reference.bytes]

type t = {
  evidence_root : string; directory : string; relative_directory : string;
  logical_event : string; buffer : bytes; mutable used : int;
  mutable ordinal : int; mutable node_ordinal : int; mutable logical_bytes : int;
  levels : (int, reference list) Hashtbl.t; mutable finished : bool;
}

let rec mkdir path =
  if not (Sys.file_exists path) then (mkdir (Filename.dirname path); Unix.mkdir path 0o700)
let create ~evidence_root ~relative_directory ~logical_event =
  if String.length logical_event > 4096 then failwith "The logical event identifier is oversized";
  if Filename.is_relative relative_directory = false ||
     List.mem ".." (String.split_on_char '/' relative_directory) then
    failwith "The chunk directory must stay inside its evidence root";
  let directory = Filename.concat evidence_root relative_directory in
  mkdir directory;
  { evidence_root; directory; relative_directory; logical_event;
    buffer = Bytes.create payload_limit; used = 0; ordinal = 0;
    node_ordinal = 0; logical_bytes = 0; levels = Hashtbl.create 8;
    finished = false }

let write_record writer name value logical_bytes =
  let data = Yojson.Safe.to_string value ^ "\n" in
  if String.length data > physical_limit then failwith "The serialized observer record exceeds 2 MiB";
  let path = Filename.concat writer.directory name in
  let channel = open_out_gen [Open_wronly; Open_creat; Open_excl; Open_binary] 0o600 path in
  Fun.protect ~finally:(fun () -> close_out channel) (fun () ->
    output_string channel data; flush channel);
  { path = Filename.concat writer.relative_directory name;
    sha256 = sha256_file path; bytes = String.length data; logical_bytes }

let index writer level (children : reference list) =
  if List.length children > children_limit || children = [] then
    failwith "The capture index has an invalid child count";
  let logical_bytes = List.fold_left (fun total (child : reference) -> total + child.logical_bytes) 0 children in
  let ordinal = writer.node_ordinal in writer.node_ordinal <- ordinal + 1;
  write_record writer (Printf.sprintf "index-%08d.json" ordinal)
    (`Assoc ["schema", `Int 2; "kind", `String "capture-index";
      "logical_event", `String writer.logical_event; "level", `Int level;
      "children", `List (List.map reference_json children);
      "logical_bytes", `Int logical_bytes]) logical_bytes

let rec push writer level (reference : reference) =
  let old = match Hashtbl.find_opt writer.levels level with None -> [] | Some x -> x in
  let children = reference :: old in
  if List.length children = children_limit then (
    Hashtbl.remove writer.levels level;
    push writer (level + 1) (index writer (level + 1) (List.rev children)))
  else Hashtbl.replace writer.levels level children

let valid_prefix buffer length =
  let byte at = Char.code (Bytes.get buffer at) in
  let rec scan at =
    if at = length then length else
    let first = byte at in
    let width = if first < 0x80 then 1
      else if first >= 0xc2 && first <= 0xdf then 2
      else if first >= 0xe0 && first <= 0xef then 3
      else if first >= 0xf0 && first <= 0xf4 then 4
      else failwith "The observer stream contains invalid UTF-8" in
    if at + width > length then at else (
      for index = 1 to width - 1 do
        if byte (at + index) land 0xc0 <> 0x80 then
          failwith "The observer stream contains an invalid UTF-8 continuation"
      done;
      if width > 1 then (
        let second = byte (at + 1) in
        if (first = 0xe0 && second < 0xa0) || (first = 0xed && second >= 0xa0) ||
           (first = 0xf0 && second < 0x90) || (first = 0xf4 && second > 0x8f) then
          failwith "The observer stream contains an invalid UTF-8 codepoint");
      scan (at + width)) in
  scan 0

let emit_leaf writer count =
  if count = 0 then () else (
    let text = Bytes.sub_string writer.buffer 0 count in
    let ordinal = writer.ordinal in writer.ordinal <- ordinal + 1;
    let reference = write_record writer (Printf.sprintf "leaf-%08d.json" ordinal)
      (`Assoc ["schema", `Int 2; "kind", `String "capture-leaf";
        "logical_event", `String writer.logical_event; "ordinal", `Int ordinal;
        "encoding", `String "utf-8"; "text", `String text;
        "text_bytes", `Int count; "payload_sha256", `String (sha256_text text)]) count in
    Bytes.blit writer.buffer count writer.buffer 0 (writer.used - count);
    writer.used <- writer.used - count;
    push writer 0 reference)

let rec substring writer text offset length =
  if writer.finished then failwith "The capture stream is already closed";
  if length <> 0 then (
    let count = min length (payload_limit - writer.used) in
    Bytes.blit_string text offset writer.buffer writer.used count;
    writer.used <- writer.used + count;
    writer.logical_bytes <- writer.logical_bytes + count;
    if writer.used = payload_limit then emit_leaf writer (valid_prefix writer.buffer writer.used);
    substring writer text (offset + count) (length - count))
let text writer value = substring writer value 0 (String.length value)

let finish writer =
  if writer.finished then failwith "The capture stream is already closed";
  let count = valid_prefix writer.buffer writer.used in
  if count <> writer.used then failwith "The capture stream ends inside a UTF-8 codepoint";
  emit_leaf writer count;
  let rec collapse () =
    let levels = Hashtbl.fold (fun level children all -> (level, children) :: all) writer.levels []
      |> List.sort (fun (left, _) (right, _) -> Int.compare left right) in
    match levels with
    | [] -> failwith "The capture stream is empty"
    | [(level, [reference])] when level > 0 -> reference
    | (level, children) :: _ ->
        Hashtbl.remove writer.levels level;
        push writer (level + 1) (index writer (level + 1) (List.rev children));
        collapse () in
  let root = collapse () in
  if root.logical_bytes <> writer.logical_bytes then failwith "The capture byte count differs";
  writer.finished <- true;
  `Assoc ["encoding", `String "json-chunks-v1"; "root", root_json root;
    "logical_bytes", `Int writer.logical_bytes]

let character writer value = text writer (String.make 1 value)
let escaped_substring writer value offset length =
  let start = ref offset in
  let flush until =
    if until > !start then substring writer value !start (until - !start) in
  for position = offset to offset + length - 1 do
    let char = value.[position] in
    let escape = match char with
      | '"' -> Some "\\\"" | '\\' -> Some "\\\\" | '\n' -> Some "\\n"
      | '\r' -> Some "\\r" | '\t' -> Some "\\t" | '\b' -> Some "\\b"
      | '\012' -> Some "\\f"
      | value when Char.code value < 32 -> Some (Printf.sprintf "\\u%04x" (Char.code value))
      | _ -> None in
    match escape with
    | None -> ()
    | Some encoded -> flush position; text writer encoded; start := position + 1
  done;
  flush (offset + length)
let string writer value =
  character writer '"'; escaped_substring writer value 0 (String.length value); character writer '"'
let pp writer document =
  character writer '"';
  let formatter = Format.make_formatter (escaped_substring writer) (fun () -> ()) in
  Format.pp_set_margin formatter 1000000;
  Format.pp_set_max_boxes formatter max_int;
  Pp.pp_with formatter document;
  Format.pp_print_flush formatter ();
  character writer '"'
let json writer = function
  | `String value -> string writer value
  | (`Null | `Bool _ | `Int _ | `Intlit _ | `Float _) as value ->
      text writer (Yojson.Safe.to_string value)
  | _ -> invalid_arg "Use the streaming object/array writer for structured JSON"
let array writer emit values =
  character writer '[';
  List.iteri (fun index value -> if index > 0 then character writer ','; emit value) values;
  character writer ']'
let object_ writer fields =
  character writer '{';
  List.iteri (fun index (name, emit) ->
    if index > 0 then character writer ','; string writer name; character writer ':'; emit ()) fields;
  character writer '}'
