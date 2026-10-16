open Kernel_store
module Chunks=Trace_block_chunks
let assoc key=function `Assoc fields->List.assoc key fields|_->failwith "Expected a kernel object"
let string=function `String value->value|_->failwith "Expected a kernel string"
let array=function `List values->values|_->failwith "Expected a kernel array"
let reference value={path=string(assoc "path" value);sha256=string(assoc "sha256" value);
  bytes=(match assoc "bytes" value with `Int bytes->bytes|_->failwith "Expected artifact bytes")}
let read root reference =
  if Kernel_store.reference root reference.path<>reference then failwith "Kernel metadata reference mismatch";
  Kernel_artifact.read root reference.path
let rec stream_json writer = function
  |`Assoc fields->Chunks.object_ writer(List.map(fun(key,value)->key,fun()->stream_json writer value)fields)
  |`List values->Chunks.array writer(stream_json writer)values
  |value->Chunks.json writer value
let pointer id =
  let escape text=String.concat "~1"(String.split_on_char '/' (String.concat "~0"(String.split_on_char '~' text)))in
  "#/displays/"^escape id
let proof_terms () =
  let state=Vernacstate.Interp.freeze_interp_state()in
  match state.Vernacstate.Interp.lemmas with
  |None->failwith "The bounded residual has no proof"
  |Some stack->Proof.partial_proof(Declare.Proof.get(Vernacstate.LemmaStack.get_top stack))
let emit ~evidence_root ~directory ~number ~include_proof writer env sigma goals fresh_counter =
  Trace_raw_budget.ensure_data();
  let manifest_path=match Sys.getenv_opt "ZESU_TRACE_KERNEL_MANIFEST"with
    |Some path->path|None->failwith "The bounded kernel manifest is unavailable"in
  if (Unix.stat manifest_path).Unix.st_size>Chunks.physical_limit then failwith "The bounded runtime manifest exceeds2MiB";
  let manifest=Yojson.Safe.from_file manifest_path in
  let toolchain_ref=reference(assoc "toolchain_ref" manifest)in
  let reader=reference(assoc "reader" manifest)in
  ignore(read evidence_root toolchain_ref);
  if Kernel_store.reference evidence_root reader.path<>reader then failwith "The kernel reader identity changed";
  let proofs=if include_proof then proof_terms()else[]in
  let snapshot=snapshot ~toolchain_hash:toolchain_ref.sha256 ~env ~sigma ~goals ~fresh_counter ~proofs in
  let store=create ~evidence_root ~directory ~toolchain_ref snapshot in
  let descriptors=Hashtbl.create 64 in
  let ordered=ref[]in
  let prepare id =
    if not(Hashtbl.mem descriptors id)then(
      let displayed=Kernel_display.render store env id in
      let path=Printf.sprintf "%s/displays/input-%08d.json" directory(List.length !ordered)in
      let reference=write_json evidence_root path displayed.json in
      Hashtbl.add descriptors id reference;ordered:=(id,reference)::!ordered)in
  let entries=Hashtbl.create(List.length snapshot.catalog)in
  List.iter(fun entry->Hashtbl.add entries entry.key entry)snapshot.catalog;
  let indexes=Hashtbl.create(List.length snapshot.catalog)in
  List.iteri(fun index entry->Hashtbl.add indexes entry.key index)snapshot.catalog;
  let current=snapshot.goals @ snapshot.shelf @ snapshot.given_up in
  List.iter(fun key->
    let entry=Hashtbl.find entries key in
    if not entry.defined then prepare(Printf.sprintf "evar/%d/conclusion" key);
    List.iteri(fun index declaration->if List.nth entry.filter index then(
      prepare(Printf.sprintf "evar/%d/hyp/%d/type" key index);
      if Option.has_some(Context.Named.Declaration.get_value declaration)then
        prepare(Printf.sprintf "evar/%d/hyp/%d/body" key index)))entry.context)current;
  List.iteri(fun index _->prepare("proof/"^string_of_int index))proofs;
  let ordered=List.rev !ordered in
  let markers=List.concat_map(fun(_,reference)->array(assoc "omitted_subtrees"(read evidence_root reference)))ordered in
  let displays=List.map(fun(id,reference)->let value=read evidence_root reference in
    `Assoc["display_ref",reference_json reference;"root_id",`String id;
      "node_ref",assoc "node_ref" value;"context_ref",assoc "context_ref" value])ordered in
  let context_ref=write_json evidence_root(directory^"/snapshot-context.json")
    (`Assoc["schema",`Int 1;"kind",`String "kernel-snapshot-context";
      "complete_sidecar",reference_json store.complete;
      "goals",`List(List.map(fun key->`Int key)snapshot.goals);
      "shelf",`List(List.map(fun key->`Int key)snapshot.shelf);
      "given_up",`List(List.map(fun key->`Int key)snapshot.given_up)])in
  let plan=write_json evidence_root(directory^"/PLAN.json")(`Assoc["schema",`Int 1;
    "complete_sidecar",reference_json store.complete;"context_ref",reference_json context_ref;
    "evar_catalog_ref",reference_json store.catalog_ref;"toolchain_ref",reference_json toolchain_ref;
    "reader",reference_json reader;"receipt_prefix",`String(directory^"/reload");
    "markers",`List markers;"displays",`List displays])in
  let stdout_relative=directory^"/reader.stdout"and stderr_relative=directory^"/reader.stderr"in
  let args=[evidence_root;full_path evidence_root plan.path;toolchain_ref.sha256;"--result-ref"]in
  let executable=full_path evidence_root reader.path in
  let status=Trace_raw_budget.with_output (full_path evidence_root stdout_relative)(fun stdout->
    Trace_raw_budget.with_output (full_path evidence_root stderr_relative)(fun stderr->
      let null=Unix.openfile "/dev/null"[Unix.O_RDONLY;Unix.O_CLOEXEC]0 in
      let pid=Fun.protect ~finally:(fun()->Unix.close null)(fun()->
        Unix.create_process executable(Array.of_list(executable::args))null
          (Unix.descr_of_out_channel stdout)(Unix.descr_of_out_channel stderr))in
      let rec wait()=try snd(Unix.waitpid[]pid)with Unix.Unix_error(Unix.EINTR,_,_)->wait()in
      wait()))in
  if status<>Unix.WEXITED 0 then failwith("Fresh kernel reload failed: "^stderr_relative);
  let result_ref=reference(assoc "result"(Kernel_artifact.read evidence_root stdout_relative))in
  let result=read evidence_root result_ref in
  let receipt=reference(assoc "receipt" result)in
  let root_receipts=array(assoc "root_receipts" result)in
  let invocation=write_json evidence_root(directory^"/INVOCATION.json")(`Assoc[
    "schema",`Int 1;"kind",`String "kernel-reader-invocation";"reader",reference_json reader;
    "arguments",`List(List.map(fun text->`String text)args);"sidecar",reference_json store.complete;
    "toolchain_ref",reference_json toolchain_ref;"marker_plan",reference_json plan;
    "exit_code",`Int 0;"receipt",reference_json receipt;
    "membership_receipts",assoc "membership_receipts" result;"root_receipts",`List root_receipts;
    "stdout",reference_json(Kernel_store.reference evidence_root stdout_relative);
    "stderr",reference_json(Kernel_store.reference evidence_root stderr_relative)])in
  let by_root=Hashtbl.create(List.length ordered)in
  List.iter(fun value->let reference=reference value in
    let content=read evidence_root reference in
    Hashtbl.add by_root(string(assoc "root_id" content))reference)root_receipts;
  let final=Hashtbl.create(List.length ordered)in
  List.iteri(fun index(id,input)->
    let value=read evidence_root input in
    let fields=match value with `Assoc fields->fields|_->assert false in
    let final_value=`Assoc(fields@[
      "display_input_ref",reference_json input;
      "reload_evidence",`Assoc["receipt",reference_json receipt;"invocation",reference_json invocation];
      "root_reload_evidence",`Assoc["receipt",reference_json(Hashtbl.find by_root id);"invocation",reference_json invocation]])in
    let reference=write_json evidence_root(Printf.sprintf "%s/displays/final-%08d.json" directory index)final_value in
    Hashtbl.add final id reference)ordered;
  let display id=read evidence_root(Hashtbl.find final id)in
  let text mode id=string(assoc(if mode then "goal_nonotation"else"goal")(display id))in
  let hyp mode key index declaration=
    let base field=Printf.sprintf "evar/%d/hyp/%d/%s" key index field in
    `Assoc["names",`List[`String(Names.Id.to_string(Context.Named.Declaration.get_id declaration))];
      "type",`String(text mode(base "type"));"type_display_ref",`String(pointer(base "type"));
      "body",(match Context.Named.Declaration.get_value declaration with None->`Null|Some _->`String(text mode(base "body")));
      "body_display_ref",(match Context.Named.Declaration.get_value declaration with None->`Null|Some _->`String(pointer(base "body")))]in
  let goal mode key=
    let entry=Hashtbl.find entries key in
    let id=Printf.sprintf "evar/%d/conclusion"key in
    `Assoc["evar",`Int key;"name",(match entry.name with None->`Null|Some name->`String name);
      "status",`String(if entry.defined then"defined"else"undefined");
      "entry_ref",`Assoc["catalog_ref",reference_json store.catalog_ref;
        "pointer",`String(Printf.sprintf "#/entries/%d"(Hashtbl.find indexes key))];
      "conclusion",(if entry.defined then`Assoc["availability",`String "unavailable";
        "reason",`String "Evd erases the conclusion of a defined evar"]else`String(text mode id));
      "display_ref",(if entry.defined then`Null else`String(pointer id));
      "body",(if entry.defined then`Assoc["availability",`String "referenced";
        "complete_sidecar",reference_json store.complete;
        "node_ref",node_json{root_id=Printf.sprintf "evar/%d/body"key;child_path=[]}]else`Null);
      "hyps",`List(List.rev(List.filter_map(fun(index,declaration)->
        if List.nth entry.filter index then Some(hyp mode key index declaration)else None)
        (List.mapi(fun index declaration->index,declaration)entry.context)))]in
  let ids values=`List(List.map(fun key->`Int key)values)in
  let hidden=`Assoc["availability",`String "unavailable";
    "reason",`String "The public API does not expose ordered hidden focus frames"]in
  let mode no_notation ()=Chunks.object_ writer[
    "goals",(fun()->Chunks.array writer(fun key->stream_json writer(goal no_notation key))snapshot.goals);
    "shelf",(fun()->Chunks.array writer(fun key->stream_json writer(goal no_notation key))snapshot.shelf);
    "given_up",(fun()->Chunks.array writer(fun key->stream_json writer(goal no_notation key))snapshot.given_up);
    "hidden_stack",(fun()->stream_json writer hidden)]in
  let evars()=Chunks.array writer(fun(index,entry)->
    let base=Printf.sprintf "evar/%d/%s"entry.key(if entry.defined then"body"else"conclusion")in
    let term_ref id=`Assoc["availability",`String "referenced";"complete_sidecar",reference_json store.complete;
      "node_ref",node_json{root_id=id;child_path=[]}]in
    stream_json writer(`Assoc["id",`Int entry.key;"defined",`Bool entry.defined;
      "type",(if entry.defined then`Assoc["availability",`String "unavailable";
        "reason",`String "Evd erases defined conclusions"]else term_ref base);
      "body",(if entry.defined then term_ref base else`Null);
      "context",`Assoc["catalog_ref",reference_json store.catalog_ref;
        "pointer",`String(Printf.sprintf "#/entries/%d/context"index)];
      "entry_ref",`Assoc["catalog_ref",reference_json store.catalog_ref;
        "pointer",`String(Printf.sprintf "#/entries/%d"index)]]))
    (List.mapi(fun index entry->index,entry)snapshot.catalog)in
  let show_proof()=Chunks.object_ writer[
    "availability",(fun()->Chunks.string writer(if include_proof then"bounded-display"else"not-requested"));
    "command",(fun()->Chunks.string writer "Show Proof.");
    "notation",(fun()->Chunks.array writer(fun(index,_)->Chunks.string writer(text false("proof/"^string_of_int index)))(List.mapi(fun index term->index,term)proofs));
    "no_notation",(fun()->Chunks.array writer(fun(index,_)->Chunks.string writer(text true("proof/"^string_of_int index)))(List.mapi(fun index term->index,term)proofs));
    "complete_sidecar",(fun()->stream_json writer(reference_json store.complete))]in
  Chunks.object_ writer[
    "schema",(fun()->Chunks.json writer(`Int 2));"surface_policy",(fun()->Chunks.string writer "bounded-kernel-v1");
    "group_policy",(fun()->Chunks.string writer "raw-ordered-goals-v1");
    "group_counts",(fun()->stream_json writer(`Assoc[
      "goals",`Int(List.length snapshot.goals);"shelf",`Int(List.length snapshot.shelf);
      "given_up",`Int(List.length snapshot.given_up)]));
    "event_sequence",(fun()->Chunks.json writer(`Int number));
    "notation",mode false;"no_notation",mode true;"evars",evars;
    "evar_catalog_ref",(fun()->stream_json writer(reference_json store.catalog_ref));
    "complete_sidecar",(fun()->stream_json writer(reference_json store.complete));
    "reload_evidence",(fun()->stream_json writer(`Assoc["receipt",reference_json receipt;"invocation",reference_json invocation]));
    "fresh_evar_counter",(fun()->Chunks.json writer(`Int fresh_counter));
    "live_goal_ids",(fun()->stream_json writer(ids snapshot.goals));
    "displays",(fun()->Chunks.object_ writer(List.map(fun(id,_)->id,fun()->stream_json writer(display id))ordered));
    "show_proof",show_proof]
