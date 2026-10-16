let ()=match Array.to_list Sys.argv with
|[_;"write";root;relative]->
    let value=`Assoc["schema",`Int 1;"kind",`String "metadata-control";
      "unicode",`String(String.concat ""(List.init 2000000(fun _->"λ")));
      "rows",`List(List.init 20000(fun index->`Assoc["index",`Int index;"text",`String "typed-marker-reference"]))]in
    Kernel_artifact.write root relative value;
    let expected=Kernel_artifact.hash_stream(fun output->Kernel_artifact.emit_json output value)in
    let actual=Kernel_artifact.read root relative in
    if actual<>value then failwith "Reconstructed JSON differs";
    print_endline(Yojson.Safe.to_string(`Assoc["accepted",`Bool true;"logical_sha256",`String expected;
      "artifact_sha256",`String(Trace_block_chunks.sha256_file(Filename.concat root relative))]))
|[_;"read";root;relative]->ignore(Kernel_artifact.read root relative);print_endline "{\"accepted\":true}"
|_->failwith "Usage: artifact_control write/read ROOT RELATIVE"
