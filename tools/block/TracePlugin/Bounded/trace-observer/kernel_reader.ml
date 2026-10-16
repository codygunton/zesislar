open Kernel_store
let assoc name=function `Assoc fields->List.assoc name fields|_->failwith "Expected an object"
let string=function `String value->value|_->failwith "Expected a string"
let integer=function `Int value->value|_->failwith "Expected an integer"
let list=function `List value->value|_->failwith "Expected an array"
let reference value={path=string(assoc "path" value);sha256=string(assoc "sha256" value);bytes=integer(assoc "bytes" value)}
let read_json root reference =
  let actual=Kernel_store.reference root reference.path in
  if actual<>reference then failwith "JSON reference mismatch";
  Kernel_artifact.read root reference.path
let node value={root_id=string(assoc "root_id" value);
  child_path=List.map integer(list(assoc "child_path" value))}
let run root plan_path expected executable =
  let relative=if Filename.is_relative plan_path then plan_path else
    let prefix=root^"/" in if String.starts_with ~prefix plan_path then
      String.sub plan_path(String.length prefix)(String.length plan_path-String.length prefix)
    else failwith "The marker plan leaves its evidence root" in
  let plan=Kernel_artifact.read root relative in
  let reader=reference(assoc "reader" plan) in
  let executable_hash=Trace_block_chunks.sha256_file executable in
  if Kernel_store.reference root reader.path<>reader || executable_hash<>reader.sha256 then
    failwith "Reader executable identity mismatch";
  let complete=reference(assoc "complete_sidecar" plan) in
  let toolchain_ref=reference(assoc "toolchain_ref" plan) in
  if toolchain_ref.sha256<>expected then failwith "Expected toolchain mismatch";
  ignore(read_json root toolchain_ref);
  let snapshot:snapshot=read_marshal root complete in
  let nodes=validate snapshot expected in
  let prefix=string(assoc "receipt_prefix" plan) in
  let remarshal=write_marshal root (prefix^"/complete-remarshal.marshal") snapshot in
  if remarshal.sha256<>complete.sha256 || remarshal.bytes<>complete.bytes then failwith "Complete remarshal mismatch";
  let catalog_ref=reference(assoc "evar_catalog_ref" plan) in
  let catalog=read_json root catalog_ref in
  if catalog <> catalog_json snapshot complete then failwith "Catalog content or association mismatch";
  let dummy={evidence_root=root;directory="";snapshot;complete;catalog_ref;toolchain_ref;
    terms=Physical.create 1;marker_count=0} in
  let receipts=List.mapi(fun index value->
    let marker_ref=reference value in
    let marker=read_json root marker_ref in
    if assoc "schema" marker<>`Int 1 || assoc "kind" marker<>`String "kernel-elision" then failwith "Marker schema mismatch";
    if assoc "evar_catalog_ref" marker<>reference_json catalog_ref || assoc "toolchain_ref" marker<>reference_json toolchain_ref then
      failwith "Marker catalog or toolchain mismatch";
    let node=node(assoc "node_ref" marker) in
    let term=resolve snapshot node in
    let sidecar=reference(assoc "sidecar" marker) in
    if assoc "sha256" marker<>`String sidecar.sha256 || assoc "bytes" marker<>`Int sidecar.bytes then failwith "Marker artifact mismatch";
    let resolved=write_marshal root (Printf.sprintf "%s/resolved-%08d.marshal" prefix index)term in
    if resolved.sha256<>sidecar.sha256 || resolved.bytes<>sidecar.bytes then failwith "Subtree membership mismatch";
    let subtree:Constr.t=read_marshal root sidecar in
    ignore subtree;
    let context_ref=reference(assoc "context_ref" marker) in
    if read_json root context_ref<>context_json dummy node then failwith "Marker binder context mismatch";
    let owner=owner_root snapshot node.root_id in
    let displays=list(assoc "displays" plan)in
    let display=List.find_opt(fun display->string(assoc "root_id" display)=owner)displays in
    let owner_display=match display with None->`Null|Some display->assoc "display_ref" display in
    let evar_fields=match assoc "reason" marker,Constr.kind term with
      |`String "evar-reference",Constr.Evar(key,_)->
          let key=Evar.repr key in
          if assoc "source_evar" marker<>`Int key || not(List.exists(fun entry->entry.key=key)snapshot.catalog)then
            failwith "Marker evar association mismatch";
          ["source_evar",`Int key]
      |`String "evar-reference",_->failwith "Marker is not an evar"
      |_,_->
          (match marker with `Assoc fields when List.mem_assoc "source_evar" fields->failwith "Unexpected source evar"|_->());[] in
    write_json root (Printf.sprintf "%s/membership-%08d.json" prefix index)
      (`Assoc(["schema",`Int 1;"kind",`String "kernel-node-membership";
        "marker_ref",reference_json marker_ref;"node_ref",node_json node;
        "owner_root_id",`String owner;"display_ref",owner_display;
        "complete_sidecar",reference_json complete;"resolved_sidecar",reference_json sidecar;
        "context_ref",reference_json context_ref;"evar_catalog_ref",reference_json catalog_ref;
        "toolchain_ref",reference_json toolchain_ref;"reader",reference_json reader;
        "accepted",`Bool true;"error",`Null;
        "checks",`List(List.map(fun x->`String x)["root-membership";"binder-context";"catalog-association";"subtree-marshal-bytes";"evar-reference"])]@evar_fields)))
      (list(assoc "markers" plan)) in
  let context_ref=reference(assoc "context_ref" plan) in
  let context=read_json root context_ref in
  (match context with
   |`Assoc fields when List.assoc_opt "kind" fields=Some(`String "kernel-snapshot-context")->
       let ids keys=`List(List.map(fun key->`Int key)keys)in
       let expected=`Assoc["schema",`Int 1;"kind",`String "kernel-snapshot-context";
         "complete_sidecar",reference_json complete;"goals",ids snapshot.goals;
         "shelf",ids snapshot.shelf;"given_up",ids snapshot.given_up]in
       if context<>expected then failwith "Snapshot raw group context mismatch"
   |_->());
  let root_receipts=List.mapi(fun index item->
    let display_ref=reference(assoc "display_ref" item) in
    let display=read_json root display_ref in
    let root_id=string(assoc "root_id" item) in
    let node=node(assoc "node_ref" item) in
    if node.root_id<>root_id || node.child_path<>[] || assoc "root_id" display<>`String root_id ||
       assoc "node_ref" display<>node_json node then failwith "Display root identity mismatch";
    if assoc "complete_sidecar" display<>reference_json complete ||
       assoc "evar_catalog_ref" display<>reference_json catalog_ref ||
       assoc "toolchain_ref" display<>reference_json toolchain_ref then failwith "Display root association mismatch";
    let context_ref=reference(assoc "context_ref" item) in
    if assoc "context_ref" display<>reference_json context_ref ||
       read_json root context_ref<>context_json dummy node then failwith "Display root context mismatch";
    let context_nodes=List.map (fun value->{root_id=string(assoc "root_id" value);child_path=List.map integer(list(assoc "child_path" value))})(list(assoc "context_roots" display))in
    let root_value=root_by_id snapshot root_id in
    let expected_contexts=context_roots root_value in
    let whole_elision=assoc "displayed_nodes" display=`Int 1 &&
      assoc "status"(assoc "print_check" display)=`String "fallback-display-budget"in
    if context_nodes<>expected_contexts && not(context_nodes=[] && whole_elision)then
      failwith "Display context root coverage mismatch";
    List.iter(fun child->
      if child.child_path<>[] || owner_root snapshot child.root_id<>root_id then failwith "Foreign display context root";
      ignore(resolve snapshot child))context_nodes;
    let term=resolve snapshot node in
    let resolved=write_marshal root (Printf.sprintf "%s/root-%08d.marshal" prefix index)term in
    write_json root (Printf.sprintf "%s/root-%08d.json" prefix index)
      (`Assoc["schema",`Int 1;"kind",`String "kernel-root-membership";
        "display_ref",reference_json display_ref;"root_id",`String root_id;"node_ref",node_json node;
        "context_roots",`List(List.map node_json context_nodes);
        "complete_sidecar",reference_json complete;"resolved_sidecar",reference_json resolved;
        "context_ref",reference_json context_ref;"evar_catalog_ref",reference_json catalog_ref;
        "toolchain_ref",reference_json toolchain_ref;"reader",reference_json reader;
        "accepted",`Bool true;"error",`Null]))(list(assoc "displays" plan)) in
  let receipt=write_json root (prefix^"/reload.json")
    (`Assoc["schema",`Int 1;"kind",`String "kernel-marshal-reload";
      "sidecar",reference_json complete;"context_ref",reference_json context_ref;
      "evar_catalog_ref",reference_json catalog_ref;"toolchain_ref",reference_json toolchain_ref;
      "reader",reference_json reader;"accepted",`Bool true;"error",`Null;
      "unique_kernel_nodes",`Int nodes;"kernel_typecheck",`String "not-attempted";
      "checks",`Assoc(List.map(fun key->key,`Bool true)
        ["hash";"bytes";"schema";"toolchain";"context";"evar_references";"remarshal_bytes";"trailing_bytes_absent"])]) in
  `Assoc["schema",`Int 1;"accepted",`Bool true;"receipt",reference_json receipt;
    "membership_receipts",`List(List.map reference_json receipts);
    "root_receipts",`List(List.map reference_json root_receipts)]
let ()=match Array.to_list Sys.argv with
 |[executable;root;plan;expected]->
    let value=run root plan expected executable in print_endline(Yojson.Safe.to_string value)
 |[executable;root;plan;expected;"--result-ref"]->
    let value=run root plan expected executable in
    let relative=Filename.dirname(String.sub plan(String.length root+1)(String.length plan-String.length root-1))in
    let result=write_json root(relative^"/READER-RESULT.json")value in
    print_endline(Yojson.Safe.to_string(`Assoc["result",reference_json result]))
 |_->failwith "Usage: kernel_reader ROOT PLAN TOOLCHAIN_SHA256 [--result-ref]"
