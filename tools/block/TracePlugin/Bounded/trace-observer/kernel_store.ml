open Names
module Chunks = Trace_block_chunks
module Physical = Hashtbl.Make(struct
  type t = Constr.t
  let equal left right = left == right
  (* Stdlib hashing has bounded traversal. Constr.hash expands shared DAGs. *)
  let hash term = Hashtbl.hash_param 10 32 term
end)

type root = {
  root_id : string;
  term : Constr.t;
  named : Constr.named_context;
  relative : Constr.rel_context;
}
type catalog_entry = {
  key : int;
  name : string option;
  defined : bool;
  conclusion : Constr.t option;
  body : Constr.t option;
  context : Constr.named_context;
  filter : bool list;
  candidates : Constr.t list option;
  relevance : Sorts.relevance;
}
type snapshot = {
  schema : int;
  magic : string;
  toolchain_hash : string;
  roots : root list;
  catalog : catalog_entry list;
  universe_state : UState.t;
  goals : int list;
  shelf : int list;
  given_up : int list;
  fresh_counter : int;
}
type reference = { path : string; sha256 : string; bytes : int }
type node_ref = { root_id : string; child_path : int list }
type marker = {
  reason : string;
  depth : int;
  sidecar : reference;
  marker_ref : reference;
  context_ref : reference;
  node_ref : node_ref;
  source_evar : int option;
  json : Yojson.Safe.t;
}
type store = {
  evidence_root : string;
  directory : string;
  snapshot : snapshot;
  complete : reference;
  catalog_ref : reference;
  toolchain_ref : reference;
  terms : reference Physical.t;
  mutable marker_count : int;
}
let reference_json reference = `Assoc ["path",`String reference.path;
  "sha256",`String reference.sha256;"bytes",`Int reference.bytes]
let node_json (node : node_ref) = `Assoc ["root_id",`String node.root_id;
  "child_path",`List(List.map (fun value -> `Int value) node.child_path)]
let full_path root relative =
  if Filename.is_relative relative && not (List.mem ".." (String.split_on_char '/' relative))
  then Filename.concat root relative else failwith "Unsafe kernel artifact path"
let reference root relative =
  let path=full_path root relative in
  {path=relative;sha256=Chunks.sha256_file path;bytes=(Unix.stat path).Unix.st_size}
let write_bytes root relative emit =
  let path=full_path root relative in Chunks.mkdir (Filename.dirname path);
  Trace_raw_budget.with_output path emit;
  reference root relative
let write_marshal root relative value = write_bytes root relative (fun channel -> Marshal.to_channel channel value [])
let write_json root relative value = Kernel_artifact.write root relative value; reference root relative
let read_marshal root reference =
  let path=full_path root reference.path in
  if Chunks.sha256_file path <> reference.sha256 || (Unix.stat path).Unix.st_size <> reference.bytes then
    failwith "Kernel artifact hash or size mismatch";
  let channel=open_in_bin path in
  Fun.protect ~finally:(fun()->close_in channel) (fun()->
    let value=Marshal.from_channel channel in
    if pos_in channel <> in_channel_length channel then failwith "Trailing kernel artifact bytes";
    value)
let raw = EConstr.Unsafe.to_constr
let context_root root_id term env =
  {root_id;term;named=Environ.named_context env;relative=Environ.rel_context env}
let snapshot ~toolchain_hash ~env ~sigma ~goals ~fresh_counter ~proofs =
  let catalog=Evd.fold (fun key (Evd.EvarInfo info) entries ->
    let defined,conclusion,body,candidates=match Evd.evar_body info with
      | Evd.Evar_empty -> false,Some(raw(Evd.evar_concl info)),None,
          Option.map (List.map raw) (Evd.evar_candidates info)
      | Evd.Evar_defined body -> true,None,Some(raw body),None in
    let context=EConstr.Unsafe.to_named_context (Evd.evar_context info) in
    {key=Evar.repr key;name=Option.map Id.to_string (Evd.evar_ident key sigma);
     defined;conclusion;body;context;candidates;relevance=Evd.evar_relevance info;
     filter=Stdlib.Option.value (Evd.Filter.repr(Evd.evar_filter info))
       ~default:(List.map(fun _->true) context)}::entries) sigma []
    |> List.sort(fun left right->Int.compare left.key right.key) in
  let roots=List.concat_map(fun entry ->
    let make label term={root_id=Printf.sprintf "evar/%d/%s" entry.key label;
      term;named=entry.context;relative=[]} in
    List.filter_map(fun (name,term)->Option.map(make name) term)
      ["conclusion",entry.conclusion;"body",entry.body] @
    (match entry.candidates with None->[]|Some terms->List.mapi(fun index term->make ("candidate/"^string_of_int index) term) terms)) catalog in
  let selected=List.map Evar.repr(goals @ Evd.shelf sigma @ Evar.Set.elements(Evd.given_up sigma))in
  let roots=roots @ List.concat_map(fun entry->if not(List.mem entry.key selected)then[]else
    List.concat(List.mapi(fun index declaration->
      let named=List.filteri(fun position _->position>index)entry.context in
      let make field term={root_id=Printf.sprintf "evar/%d/hyp/%d/%s" entry.key index field;
        term;named;relative=[]}in
      make "type"(Context.Named.Declaration.get_type declaration)::
      (match Context.Named.Declaration.get_value declaration with None->[]|Some body->[make "body" body]))entry.context))catalog in
  let roots=roots @ List.mapi(fun index term->context_root ("proof/"^string_of_int index) (raw term) env) proofs in
  {schema=1;magic="p0-bounded-kernel-snapshot";toolchain_hash;roots;catalog;
   universe_state=Evd.evar_universe_context sigma;
   goals=List.map Evar.repr goals;shelf=List.map Evar.repr(Evd.shelf sigma);
   given_up=List.map Evar.repr(Evar.Set.elements(Evd.given_up sigma));fresh_counter}
let selected_ids snapshot=List.sort_uniq Int.compare(snapshot.goals @ snapshot.shelf @ snapshot.given_up)
let emit_catalog ?(compact=true) output snapshot complete =
  let text value=output value 0(String.length value)in
  let json value=Kernel_artifact.emit_json output value in
  let object_ fields=text "{";List.iteri(fun index(key,emit)->
    if index>0 then text ",";json(`String key);text ":";emit())fields;text "}"in
  let array emit values=text "[";List.iteri(fun index value->if index>0 then text ",";emit value)values;text "]"in
  let selected=selected_ids snapshot in
  let term_ref id=`Assoc["availability",`String "referenced";
    "complete_sidecar",reference_json complete;"node_ref",node_json{root_id=id;child_path=[]}]in
  object_(["schema",(fun()->json(`Int(if compact then 2 else 1)));"complete_sidecar",(fun()->json(reference_json complete))] @
    (if compact then ["selected_ids",(fun()->array(fun key->json(`Int key))selected)]else[]) @ [
    "entries",(fun()->array(fun(index,entry)->
      let base=Printf.sprintf "evar/%d/%s"entry.key(if entry.defined then "body"else"conclusion")in
      let count=List.length entry.context in
      let compact_field field count=`Assoc["availability",`String "referenced";
        "complete_sidecar",reference_json complete;"catalog_index",`Int index;
        "evar",`Int entry.key;"field",`String field;"count",`Int count]in
      object_["id",(fun()->json(`Int entry.key));
        "name",(fun()->json(match entry.name with None->`Null|Some name->`String name));
        "defined",(fun()->json(`Bool entry.defined));
        "type",(fun()->json(if entry.defined then`Assoc["availability",`String "unavailable";
          "reason",`String "Evd erases the conclusion of a defined evar"]else term_ref base));
        "body",(fun()->json(if entry.defined then term_ref base else`Null));
        "context",(fun()->if not compact || List.mem entry.key selected then
          array(fun(index,declaration)->
            let root field=Printf.sprintf "%s@named:%d:%s"base index field in
            json(`Assoc["name",`String(Id.to_string(Context.Named.Declaration.get_id declaration));
              "type",term_ref(root "type");"body",(match Context.Named.Declaration.get_value declaration with
                None->`Null|Some _->term_ref(root "body"))]))
            (List.mapi(fun index declaration->index,declaration)entry.context)
          else json(compact_field "context" count));
        "context_declarations",(fun()->json(`Int count));
        "filter",(fun()->if not compact || List.mem entry.key selected then array(fun value->json(`Bool value))entry.filter
          else json(compact_field "filter"(List.length entry.filter)));
        "candidates",(fun()->match entry.candidates with None->json`Null|Some values->
          array(fun(index,_)->json(term_ref(Printf.sprintf "evar/%d/candidate/%d"entry.key index)))
            (List.mapi(fun index term->index,term)values));
        "candidate_count",(fun()->json(match entry.candidates with None->`Null|Some values->`Int(List.length values)))])
      (List.mapi(fun index entry->index,entry)snapshot.catalog))])
let create ~evidence_root ~directory ~toolchain_ref snapshot =
  if snapshot.toolchain_hash <> toolchain_ref.sha256 then failwith "Toolchain association mismatch";
  let complete=write_marshal evidence_root (directory^"/complete.marshal") snapshot in
  let catalog_path=directory^"/evar-catalog.json"in
  Kernel_artifact.write_stream evidence_root catalog_path(fun output->emit_catalog output snapshot complete);
  let catalog_ref=reference evidence_root catalog_path in
  {evidence_root;directory;snapshot;complete;catalog_ref;toolchain_ref;
   terms=Physical.create 1024;marker_count=0}
let term_artifact store term =
  match Physical.find_opt store.terms term with
  | Some reference->reference
  | None ->
      let relative=Printf.sprintf "%s/terms/%08d.marshal" store.directory (Physical.length store.terms) in
      let reference=write_marshal store.evidence_root relative term in
      Physical.add store.terms term reference;reference
let children term = let reversed=ref [] in Constr.iter(fun child->reversed:=child::!reversed)term;List.rev !reversed
let arity_up_to limit term =
  let count=ref 0 in let exception Too_wide in
  try Constr.iter(fun _->incr count;if !count>limit then raise Too_wide)term;Some !count
  with Too_wide->None
let root_by_id snapshot id =
  match List.find_opt(fun(root:root)->root.root_id=id)snapshot.roots with
  | Some root->root
  | None ->
      (* Context roots use explicit declaration indices. The complete snapshot retains these terms. *)
      let parts=String.split_on_char '@' id in
      match parts with
      | [base;spec] ->
          let root=List.find(fun(root:root)->root.root_id=base)snapshot.roots in
          let fields=String.split_on_char ':' spec in
          (match fields with
           | ["named";index;field] ->
               let index=int_of_string index in
               let declaration=List.nth root.named index in
               let term=match field with "type"->Context.Named.Declaration.get_type declaration
                 | "body"->Option.get(Context.Named.Declaration.get_value declaration)
                 | _->failwith "Unknown context field" in
               {root_id=id;term;named=List.tl(List.filteri(fun n _->n>=index)root.named);relative=[]}
           | ["rel";index;field] ->
               let index=int_of_string index in
               let declaration=List.nth root.relative index in
               let term=match field with "type"->Context.Rel.Declaration.get_type declaration
                 | "body"->Option.get(Context.Rel.Declaration.get_value declaration)
                 | _->failwith "Unknown context field" in
               {root_id=id;term;named=root.named;relative=List.tl(List.filteri(fun n _->n>=index)root.relative)}
           | _->failwith "Unknown context root")
      | _->failwith "Unknown kernel root"
let owner_root snapshot id =
  match List.find_opt(fun(root:root)->root.root_id=id)snapshot.roots with
  |Some root->root.root_id
  |None->
      ignore(root_by_id snapshot id);
      (match String.split_on_char '@' id with
       |[base;_]->if List.exists(fun(root:root)->root.root_id=base)snapshot.roots then base
         else failwith "Missing context owner"
       |_->failwith "Invalid context owner")
let context_roots (root:root) =
  let named=List.mapi(fun index declaration->index,declaration)root.named |>List.rev in
  let relative=List.mapi(fun index declaration->index,declaration)root.relative |>List.rev in
  List.concat_map(fun(index,declaration)->
    let base=Printf.sprintf "%s@named:%d:" root.root_id index in
    {root_id=base^"type";child_path=[]}::
    (if Option.has_some(Context.Named.Declaration.get_value declaration)then
      [{root_id=base^"body";child_path=[]}]else[]))named @
  List.concat_map(fun(index,declaration)->
    let base=Printf.sprintf "%s@rel:%d:" root.root_id index in
    {root_id=base^"type";child_path=[]}::
    (if Option.has_some(Context.Rel.Declaration.get_value declaration)then
      [{root_id=base^"body";child_path=[]}]else[]))relative
let resolve snapshot (node : node_ref) =
  let root=root_by_id snapshot node.root_id in
  List.fold_left(fun term index->
    if index<0 then failwith "Negative kernel child index";
    List.nth(children term)index)root.term node.child_path
let binder_trail root path =
  let name annotation=match annotation.Context.binder_name with
    |Name id->Id.to_string id|Anonymous->"_" in
  let rec walk term ancestors = function
    |[]->[]
    |index::rest->
      let bound=match Constr.kind term with
        |Constr.Prod(annotation,_,_)|Constr.Lambda(annotation,_,_) when index=1->[name annotation]
        |Constr.LetIn(annotation,_,_,_)when index=2->[name annotation]
        |Constr.Fix(_, (names,types,_))|Constr.CoFix(_, (names,types,_))when index>=Array.length types->Array.to_list(Array.map name names)
        |Constr.Case(_,_,parameters,((names,_),_),invert,_,branches)->
            let count=Array.length parameters in
            let inversion=match invert with Constr.NoInvert->0|Constr.CaseInvert{indices}->Array.length indices in
            if index=count then Array.to_list(Array.map name names)
            else if index>=count+inversion+2 then
              let names,_=branches.(index-count-inversion-2)in Array.to_list(Array.map name names)
            else []
        |_->[] in
      let row=`Assoc["parent_path",`List(List.map(fun n->`Int n)(List.rev ancestors));
        "child",`Int index;"bound_names",`List(List.map(fun n->`String n)bound)]in
      row::walk(List.nth(children term)index)(index::ancestors)rest
  in walk root [] path
let context_json store (node : node_ref) =
  let root=root_by_id store.snapshot node.root_id in
  (* This descriptor denotes exact raw binder/context data inside the complete artifact. *)
  `Assoc["schema",`Int 1;"kind",`String "kernel-node-context";
    "complete_sidecar",reference_json store.complete;"node_ref",node_json node;
    "named_declarations",`Int(List.length root.named);"relative_declarations",`Int(List.length root.relative);
    "binder_trail",`List(binder_trail root.term node.child_path)]
let context_ref store node =
  let value=context_json store node in
  let text=Yojson.Safe.to_string value ^ "\n" in
  let hash=Chunks.sha256_text text in
  let path=store.directory^"/contexts/"^hash^".json" in
  if Sys.file_exists(full_path store.evidence_root path)then(
    let actual=reference store.evidence_root path in
    if actual.sha256<>hash then failwith "Context artifact conflict";actual)
  else write_json store.evidence_root path value
let marker store ~reason ~depth ~node term =
  let sidecar=term_artifact store term in
  let context_ref=context_ref store node in
  let source_evar=match Constr.kind term with Constr.Evar(key,_)->Some(Evar.repr key)|_->None in
  let fields=["schema",`Int 1;"kind",`String "kernel-elision";"reason",`String reason;
    "depth",`Int depth;"sha256",`String sidecar.sha256;"bytes",`Int sidecar.bytes;
    "hash_scope",`String "pinned-marshal-bytes";"size_unit",`String "bytes";
    "sidecar",reference_json sidecar;"context_ref",reference_json context_ref;
    "evar_catalog_ref",reference_json store.catalog_ref;"toolchain_ref",reference_json store.toolchain_ref;
    "node_ref",node_json node] in
  let fields=match reason,source_evar with
    | "evar-reference",Some value->fields@["source_evar",`Int value]
    | "evar-reference",None->failwith "Evar marker without source evar"
    | _->fields in
  let json=`Assoc fields in
  let marker_ref=write_json store.evidence_root
    (Printf.sprintf "%s/markers/%08d.json" store.directory store.marker_count)json in
  store.marker_count<-store.marker_count+1;
  {reason;depth;sidecar;marker_ref;context_ref;node_ref=node;
   source_evar=(if reason="evar-reference" then source_evar else None);json}
let validate snapshot expected =
  if snapshot.schema<>1 || snapshot.magic<>"p0-bounded-kernel-snapshot" || snapshot.toolchain_hash<>expected then
    failwith "Snapshot schema or toolchain mismatch";
  let root_ids=Hashtbl.create(List.length snapshot.roots)in
  List.iter(fun(root:root)->
    if Hashtbl.mem root_ids root.root_id then failwith "Duplicate kernel root";
    Hashtbl.add root_ids root.root_id root)snapshot.roots;
  let catalog=Hashtbl.create(List.length snapshot.catalog) in
  List.iter(fun entry->
    if entry.key<0 || Hashtbl.mem catalog entry.key then failwith "Invalid catalog identity";
    if List.length entry.filter<>List.length entry.context then failwith "Catalog filter mismatch";
    if entry.defined<>Option.has_some entry.body || entry.defined=Option.has_some entry.conclusion then
      failwith "Catalog status mismatch";
    let check label term=Option.iter(fun term->
      let id=Printf.sprintf "evar/%d/%s"entry.key label in
      let root=try Hashtbl.find root_ids id with Not_found->failwith "Missing catalog term root"in
      if root.term != term || root.named != entry.context || root.relative<>[]then
        failwith "Catalog term/context root association mismatch")term in
    check "conclusion"entry.conclusion;check "body"entry.body;
    Option.iter(List.iteri(fun index term->check("candidate/"^string_of_int index)(Some term)))entry.candidates;
    Hashtbl.add catalog entry.key entry)snapshot.catalog;
  List.iter(fun key->if not(Hashtbl.mem catalog key)then failwith "Raw group has no catalog entry")
    (snapshot.goals @ snapshot.shelf @ snapshot.given_up);
  let seen=Physical.create 4096 in
  let pending=Stack.create() in
  let add term=Stack.push term pending in
  let named declaration=Context.Named.Declaration.iter_constr add declaration in
  let relative declaration=Context.Rel.Declaration.iter_constr add declaration in
  List.iter(fun(root:root)->add root.term;List.iter named root.named;List.iter relative root.relative)snapshot.roots;
  List.iter(fun entry->List.iter named entry.context;Option.iter add entry.conclusion;
    Option.iter add entry.body;Option.iter(List.iter add)entry.candidates)snapshot.catalog;
  while not(Stack.is_empty pending)do
    let term=Stack.pop pending in
    if not(Physical.mem seen term)then(
      Physical.add seen term ();
      (match Constr.kind term with
       | Constr.Evar(key,_)->if not(Hashtbl.mem catalog(Evar.repr key))then failwith "Dangling evar reference"
       | _->());Constr.iter add term)
  done;
  ignore(UState.context_set snapshot.universe_state);
  Physical.length seen

(* Constr.map visits some children in a different order from Constr.iter. *)
let map_indexed callback term =
  let next=ref 0 in
  let map child=let index= !next in incr next;callback index child in
  let array values=Array.map map values in
  let mapped=match Constr.kind term with
  | (Constr.Rel _|Constr.Var _|Constr.Meta _|Constr.Sort _|Constr.Const _
    |Constr.Ind _|Constr.Construct _|Constr.Int _|Constr.Float _)as atom->atom
  | Constr.Evar _->failwith "Raw evars must become detached reference holes"
  | Constr.Cast(value,kind,typ)->let value=map value in let typ=map typ in Constr.Cast(value,kind,typ)
  | Constr.Prod(name,typ,body)->let typ=map typ in let body=map body in Constr.Prod(name,typ,body)
  | Constr.Lambda(name,typ,body)->let typ=map typ in let body=map body in Constr.Lambda(name,typ,body)
  | Constr.LetIn(name,value,typ,body)->let value=map value in let typ=map typ in let body=map body in Constr.LetIn(name,value,typ,body)
  | Constr.App(fn,args)->let fn=map fn in let args=array args in Constr.App(fn,args)
  | Constr.Proj(name,relevance,value)->Constr.Proj(name,relevance,map value)
  | Constr.Case(info,univs,parameters,((names,predicate),relevance),invert,value,branches)->
      let parameters=array parameters in
      let predicate=map predicate in
      let invert=match invert with Constr.NoInvert->Constr.NoInvert
        |Constr.CaseInvert{indices}->Constr.CaseInvert{indices=array indices}in
      let value=map value in
      let branches=Array.map(fun(names,body)->names,map body)branches in
      Constr.Case(info,univs,parameters,((names,predicate),relevance),invert,value,branches)
  | Constr.Fix(index,(names,types,bodies))->let types=array types in let bodies=array bodies in Constr.Fix(index,(names,types,bodies))
  | Constr.CoFix(index,(names,types,bodies))->let types=array types in let bodies=array bodies in Constr.CoFix(index,(names,types,bodies))
  | Constr.Array(univs,values,default,typ)->let values=array values in let default=map default in let typ=map typ in Constr.Array(univs,values,default,typ)
  in Constr.of_kind mapped
