module Chunks=Trace_block_chunks
let assoc key=function `Assoc fields->List.assoc key fields|_->failwith "Expected a JSON object"
let string=function `String value->value|_->failwith "Expected a JSON string"
let integer=function `Int value->value|_->failwith "Expected a JSON integer"
let array=function `List values->values|_->failwith "Expected a JSON array"
let full root relative=
  if not(Filename.is_relative relative)||List.mem ".."(String.split_on_char '/' relative)then failwith "Unsafe artifact path";
  Filename.concat root relative
let hash_stream emit =
  let input_read,input_write=Unix.pipe ~cloexec:true()in
  let output_read,output_write=Unix.pipe ~cloexec:true()in
  let pid=Unix.create_process "sha256sum" [|"sha256sum";"--binary"|]input_read output_write Unix.stderr in
  Unix.close input_read;Unix.close output_write;
  let incoming=Unix.in_channel_of_descr output_read in
  let outgoing=Unix.out_channel_of_descr input_write in
  Fun.protect ~finally:(fun()->close_out_noerr outgoing;close_in_noerr incoming)
    (fun()->
      let answer=try emit(fun text offset count->output_substring outgoing text offset count);None
        with error->Some error in
      close_out outgoing;
      let line=input_line incoming in
      let status=snd(Unix.waitpid[]pid)in
      match answer,status with
      |Some error,_->raise error
      |None,Unix.WEXITED 0->Chunks.checked_hash line
      |_->failwith "The artifact hash process failed")
let rec emit_json output value =
  let text value=output value 0(String.length value)in
  let quoted value=
    text "\"";
    let start=ref 0 in
    let flush until=
      let rec write offset remaining=if remaining>0 then(
        let count=min remaining 65536 in output value offset count;write(offset+count)(remaining-count))in
      write !start(until- !start)in
    String.iteri(fun index char->let encoded=match char with
      |'"'->Some "\\\""|'\\'->Some "\\\\"|'\n'->Some "\\n"|'\r'->Some "\\r"|'\t'->Some "\\t"
      |'\b'->Some "\\b"|'\012'->Some "\\f"
      |char when Char.code char<32->Some(Printf.sprintf "\\u%04x"(Char.code char))|_->None in
      match encoded with None->()|Some value->flush index;text value;start:=index+1)value;
    flush(String.length value);text "\"" in
  match value with
  |`Assoc fields->text "{";List.iteri(fun index(key,value)->if index>0 then text ",";quoted key;text ":";emit_json output value)fields;text "}"
  |`List values->text "[";List.iteri(fun index value->if index>0 then text ",";emit_json output value)values;text "]"
  |`String value->quoted value
  |(`Null|`Bool _|`Int _|`Intlit _|`Float _)as value->text(Yojson.Safe.to_string value)
  |_->failwith "Unsupported kernel JSON value"
let write root relative value =
  let path=full root relative in Chunks.mkdir(Filename.dirname path);
  let buffer=Buffer.create 4096 in
  let exception Oversized in
  let small=try emit_json(fun value offset count->
      if count>Chunks.physical_limit-1-Buffer.length buffer then raise Oversized;
      Buffer.add_substring buffer value offset count)value;Some(Buffer.contents buffer^"\n")
    with Oversized->None in
  let data=match small with
    |Some data->data
    |None->
        let logical_event="kernel-json/"^relative in
        let writer=Chunks.create ~evidence_root:root ~relative_directory:(relative^".chunks")~logical_event in
        let logical_sha256=hash_stream(fun hash->emit_json(fun value offset count->
          Chunks.substring writer value offset count;hash value offset count)value)in
        let payload=Chunks.finish writer in
        Yojson.Safe.to_string(`Assoc["schema",`Int 2;"kind",`String "kernel-json-artifact";
          "logical_event",`String logical_event;"logical_sha256",`String logical_sha256;"payload",payload])^"\n" in
  if String.length data>Chunks.physical_limit then failwith "Kernel artifact wrapper exceeds 2 MiB";
  let channel=open_out_gen[Open_wronly;Open_creat;Open_excl;Open_binary]0o600 path in
  Fun.protect ~finally:(fun()->close_out channel)(fun()->output_string channel data;flush channel)
let plain_json root reference =
  let relative=string(assoc "path" reference)in
  let path=full root relative in
  let size=(Unix.stat path).Unix.st_size in
  if size>Chunks.physical_limit || size<>integer(assoc "bytes" reference) ||
     Chunks.sha256_file path<>string(assoc "sha256" reference)then failwith "Kernel JSON node identity mismatch";
  Yojson.Safe.from_file path
let read root relative =
  let path=full root relative in
  if (Unix.stat path).Unix.st_size>Chunks.physical_limit then failwith "Kernel JSON artifact exceeds 2 MiB";
  let value=Yojson.Safe.from_file path in
  match value with
  |`Assoc fields when List.assoc_opt "kind" fields=Some(`String "kernel-json-artifact")->
      if assoc "schema" value<>`Int 2 || assoc "logical_event" value<>`String("kernel-json/"^relative)then
        failwith "Kernel JSON envelope identity mismatch";
      let payload=assoc "payload" value in
      if assoc "encoding" payload<>`String "json-chunks-v1"then failwith "Unknown kernel JSON encoding";
      let logical_event="kernel-json/"^relative in
      let expected_bytes=integer(assoc "logical_bytes" payload)in
      let make_iterator()=
        let stack=ref[assoc "root" payload,None]in
        let seen=Hashtbl.create 64 in
        let ordinal=ref 0 in
        let rec next()=match !stack with
          |[]->None
          |(reference,expected_level)::rest->stack:=rest;
              let path=string(assoc "path" reference)in
              if Hashtbl.mem seen path then failwith "Repeated kernel chunk node";
              Hashtbl.add seen path();
              let value=plain_json root reference in
              if assoc "schema" value<>`Int 2 || assoc "logical_event" value<>`String logical_event then failwith "Kernel chunk identity mismatch";
              (match assoc "kind" value with
               |`String "capture-leaf"->
                   if (match expected_level with None->false|Some n->n<>0)then failwith "Kernel leaf level mismatch";
                   let text=string(assoc "text" value)in
                   if assoc "ordinal" value<>`Int !ordinal || assoc "encoding" value<>`String "utf-8" ||
                      assoc "text_bytes" value<>`Int(String.length text)||String.length text>Chunks.payload_limit ||
                      assoc "payload_sha256" value<>`String(Chunks.sha256_text text)then failwith "Kernel leaf payload mismatch";
                   if Chunks.valid_prefix(Bytes.of_string text)(String.length text)<>String.length text then
                     failwith "Kernel leaf ends inside a UTF-8 codepoint";
                   (match List.assoc_opt "logical_bytes" (match reference with `Assoc fields->fields|_->[])with
                    |Some(`Int n)when n<>String.length text->failwith "Kernel leaf reference length mismatch"|_->());
                   incr ordinal;Some text
               |`String "capture-index"->
                   let level=integer(assoc "level" value)in
                   if level<1||level>64||(match expected_level with None->false|Some n->n<>level)then failwith "Kernel index level mismatch";
                   let children=array(assoc "children" value)in
                   if children=[]||List.length children>Chunks.children_limit then failwith "Kernel index child count mismatch";
                   let bytes=List.fold_left(fun count child->count+integer(assoc "logical_bytes" child))0 children in
                   if assoc "logical_bytes" value<>`Int bytes then failwith "Kernel index byte count mismatch";
                   (match List.assoc_opt "logical_bytes" (match reference with `Assoc fields->fields|_->[])with
                    |Some(`Int n)when n<>bytes->failwith "Kernel index reference length mismatch"|_->());
                   stack:=List.map(fun child->child,Some(level-1))children @ !stack;next()
               |_->failwith "Unknown kernel chunk kind")
        in next in
      let total=ref 0 in
      let digest=hash_stream(fun hash->let next=make_iterator()in
        let rec consume()=match next()with None->()|Some text->
          total:= !total+String.length text;hash text 0(String.length text);consume()in consume())in
      if !total<>expected_bytes || digest<>string(assoc "logical_sha256" value)then failwith "Kernel logical JSON identity mismatch";
      let next=make_iterator()in
      let current=ref ""and offset=ref 0 in
      let rec supply buffer count=
        if !offset<String.length !current then(
          let amount=min count(String.length !current- !offset)in
          Bytes.blit_string !current !offset buffer 0 amount;offset:= !offset+amount;amount)
        else match next()with None->0|Some text->current:=text;offset:=0;supply buffer count in
      let lexbuf=Lexing.from_function supply in
      Yojson.Safe.from_lexbuf(Yojson.Safe.init_lexer())lexbuf
  |_->value
