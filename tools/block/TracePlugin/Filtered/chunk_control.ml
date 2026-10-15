module C = Filtered_trace_plugin.Chunks
let () =
  let root = Sys.argv.(1) in
  let source = Sys.argv.(2) in
  let relative_directory, logical_event =
    if Array.length Sys.argv = 5 then Sys.argv.(3), Sys.argv.(4)
    else "chunks/control", "control" in
  let channel = open_in_bin source in
  Unix.set_close_on_exec (Unix.descr_of_in_channel channel);
  let writer = C.create ~evidence_root:root ~relative_directory ~logical_event in
  let buffer = Bytes.create 65537 in
  let rec loop () =
    let count = input channel buffer 0 (Bytes.length buffer) in
    if count > 0 then (C.substring writer (Bytes.unsafe_to_string buffer) 0 count; loop ()) in
  loop (); close_in channel;
  let result = C.finish writer in
  print_endline (Yojson.Safe.to_string result)
