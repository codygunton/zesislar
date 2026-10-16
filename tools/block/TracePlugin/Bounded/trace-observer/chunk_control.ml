module C=Trace_block_chunks
let ()=
  let root=Sys.argv.(1)and source=Sys.argv.(2)in
  let directory=Sys.argv.(3)and logical_event=Sys.argv.(4)in
  let channel=open_in_bin source in
  let writer=C.create ~evidence_root:root ~relative_directory:directory ~logical_event in
  let buffer=Bytes.create 65537 in
  Fun.protect ~finally:(fun()->close_in_noerr channel)(fun()->
    let rec loop()=let count=input channel buffer 0(Bytes.length buffer)in
      if count>0 then(C.substring writer(Bytes.unsafe_to_string buffer)0 count;loop())in
    loop());
  print_endline(Yojson.Safe.to_string(C.finish writer))
