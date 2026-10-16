open Names
open Kernel_store
exception Display_budget
exception Placeholder_typecheck of string
let depth_limit=60
let node_limit=20000
let text_limit=1048576
let with_summary callback =
  let interp=Summary.Interp.freeze_summaries() in
  let synterp=Summary.Synterp.freeze_summaries() in
  Fun.protect ~finally:(fun()->Summary.Synterp.unfreeze_summaries synterp;
    Summary.Interp.unfreeze_summaries interp)callback
let with_printing no_notation callback =
  let settings=[Constrextern.print_no_symbol,no_notation;
    Constrextern.print_implicits,no_notation;Constrextern.print_coercions,no_notation;
    Constrextern.print_universes,no_notation;Constrextern.print_projections,false;
    Detyping.print_evar_arguments,false] in
  let old=List.map(fun(reference,_)->reference,!reference)settings in
  List.iter(fun(reference,value)->reference:=value)settings;
  Fun.protect ~finally:(fun()->List.iter(fun(reference,value)->reference:=value)old)callback
let bounded_pp document =
  let buffer=Buffer.create 4096 in
  let count=ref 0 in
  let append text start length=
    if length>text_limit - !count then raise Display_budget;
    count:= !count+length;Buffer.add_substring buffer text start length in
  let formatter=Format.make_formatter append (fun()->()) in
  Format.pp_set_max_boxes formatter max_int;
  Format.pp_set_margin formatter 120;
  (* The document belongs only to the truncated display term. *)
  Pp.pp_with formatter document;Format.pp_print_flush formatter();Buffer.contents buffer
let atom term=match Constr.kind term with
  | Constr.Rel _|Constr.Var _|Constr.Meta _|Constr.Sort _|Constr.Const _
  | Constr.Ind _|Constr.Construct _|Constr.Int _|Constr.Float _->true
  | _->false
let kernel_surface term holes =
  let buffer=Buffer.create 4096 in
  let append text=if String.length text>text_limit-Buffer.length buffer then raise Display_budget else Buffer.add_string buffer text in
  let rec render term =
    match Constr.kind term with
    | Constr.Evar(key,_) ->
        (match List.assoc_opt(Evar.repr key)holes with
         |Some name->append("?"^name)
         |None->failwith "The detached display contains an unbound hole")
    | kind ->
        let name=match kind with
          | Constr.Rel n->"Rel "^string_of_int n|Constr.Var id->"Var "^Id.to_string id
          | Constr.Meta n->"Meta "^string_of_int n
          | Constr.Sort _->"Sort"|Constr.Const(c,_)->"Const "^Constant.to_string c
          | Constr.Ind((name,n),_)->"Ind "^MutInd.to_string name^" "^string_of_int n
          | Constr.Construct(((name,n),k),_)->"Construct "^MutInd.to_string name^" "^string_of_int n^" "^string_of_int k
          | Constr.Cast _->"Cast"|Constr.Prod _->"Prod"|Constr.Lambda _->"Lambda"
          | Constr.LetIn _->"LetIn"|Constr.App _->"App"|Constr.Case _->"Case"
          | Constr.Fix _->"Fix"|Constr.CoFix _->"CoFix"|Constr.Proj _->"Proj"
          | Constr.Int n->"Int "^Uint63.to_string n|Constr.Float n->"Float "^Float64.to_string n
          | Constr.Array _->"Array"|Constr.Evar _->assert false in
        append("("^name);Constr.iter(fun child->append " ";render child)term;append ")"
  in render term;Buffer.contents buffer

type display = { json:Yojson.Safe.t; notation:string; no_notation:string; omitted:marker list;
  charged_placeholders:int; allocated_placeholders:int }
let render store globals root_id = with_summary(fun()->
  let root=root_by_id store.snapshot root_id in
  let env=ref(Environ.reset_context globals) in
  let sigma=ref(Evd.from_ctx store.snapshot.universe_state) in
  let remaining=ref node_limit in
  let reserved=ref 0 in
  let charged_placeholders=ref 0 in
  let charge()=
    if !remaining<= !reserved then failwith "Display reservation invariant failed";
    decr remaining;ref true in
  let seen=Physical.create 4096 in
  let omitted=ref [] in
  let holes=ref [] in
  let hole_markers=ref [] in
  let displayed_contexts=ref []in
  let hole_nodes=ref [] in
  let omit token reason depth node term =
    if not !token then failwith "A display node charge was reused";
    token:=false;incr charged_placeholders;
    if List.length !hole_nodes>=node_limit then failwith "Detached hole budget exceeded";
    let marker=marker store ~reason ~depth ~node term in
    let name=Printf.sprintf "elided_%s_%d" (String.sub marker.sidecar.sha256 0 8) (List.length !omitted) in
    let next,(typ,_)=Evarutil.new_type_evar !env !sigma Evd.univ_flexible in
    let next,hole=Evarutil.new_evar ~typeclass_candidate:false
      ~naming:(Namegen.IntroFresh(Id.of_string name)) !env next typ in
    sigma:=next;
    let raw=EConstr.Unsafe.to_constr hole in
    let key=match Constr.kind raw with Constr.Evar(key,_)->key|_->assert false in
    holes:=(Evar.repr key,name)::!holes;
    hole_markers:=(Evar.repr key,name,marker)::!hole_markers;hole_nodes:=key::!hole_nodes;
    omitted:=marker::!omitted;raw in
  let rec truncate root_id path depth term =
    let node={root_id;child_path=List.rev path} in
    let token=charge()in
    match Constr.kind term with
    | Constr.Evar _->omit token "evar-reference" depth node term
    | _ when not(atom term) && Physical.mem seen term ->omit token "shared-reference" depth node term
    | _ when depth>=depth_limit && not(atom term)->omit token "depth-limit" depth node term
    | _ ->
        (match arity_up_to (!remaining - !reserved) term with
         | None->omit token "node-budget" depth node term
         | Some count->
             if not(atom term)then Physical.add seen term ();
             map_indexed(fun index term->
               let old= !reserved in reserved:=old+count-index-1;
               Fun.protect ~finally:(fun()->reserved:=old)
                 (fun()->truncate root_id (index::path)(depth+1)term))term) in
  let fields_named=List.fold_left(fun count declaration->count+1+
    (if Option.has_some(Context.Named.Declaration.get_value declaration)then 1 else 0))0 root.named in
  let fields_relative=List.fold_left(fun count declaration->count+1+
    (if Option.has_some(Context.Rel.Declaration.get_value declaration)then 1 else 0))0 root.relative in
  let pending=ref(1+fields_named+fields_relative)in
  let top id term =
    if id<>root_id then displayed_contexts:={root_id=id;child_path=[]}::!displayed_contexts;
    let old= !reserved in reserved:= !pending-1;
    Fun.protect ~finally:(fun()->reserved:=old;decr pending)
      (fun()->truncate id [] 0 term)in
  let truncated,forced_budget=if !pending>node_limit then(
    let token=charge()in
    omit token "node-budget" 0 {root_id;child_path=[]}root.term,
    Some "The context exceeds the detached display node budget")else(
  let named=List.mapi(fun index declaration->index,declaration)root.named |> List.rev in
  List.iter(fun(index,declaration)->
    let base=Printf.sprintf "%s@named:%d:" root_id index in
    let typ=top(base^"type")(Context.Named.Declaration.get_type declaration) in
    let declaration=match Context.Named.Declaration.get_value declaration with
      |None->Context.Named.Declaration.LocalAssum(Context.Named.Declaration.get_annot declaration,typ)
      |Some body->Context.Named.Declaration.LocalDef(Context.Named.Declaration.get_annot declaration,
        top(base^"body") body,typ) in
    env:=Environ.push_named declaration !env)named;
  let relative=List.mapi(fun index declaration->index,declaration)root.relative |> List.rev in
  List.iter(fun(index,declaration)->
    let base=Printf.sprintf "%s@rel:%d:" root_id index in
    let typ=top(base^"type")(Context.Rel.Declaration.get_type declaration) in
    let declaration=match Context.Rel.Declaration.get_value declaration with
      |None->Context.Rel.Declaration.LocalAssum(Context.Rel.Declaration.get_annot declaration,typ)
      |Some body->Context.Rel.Declaration.LocalDef(Context.Rel.Declaration.get_annot declaration,
        top(base^"body") body,typ) in
    env:=Environ.push_rel declaration !env)relative;
  top root_id root.term,None) in
  let typecheck () =
    try
      (* Both context and term contain only detached, truncated data. *)
      let checked,_=Typing.type_of !env !sigma (EConstr.of_constr truncated) in
      if List.exists(fun key->Evd.is_defined checked key)!hole_nodes then
        raise(Placeholder_typecheck "Typechecking defined a display-only hole");
      sigma:=checked
    with error when CErrors.noncritical error->
      raise(Placeholder_typecheck(Printexc.to_string error)) in
  let fallback reason status =
    let text=try kernel_surface truncated !holes with Display_budget ->
      (* Replace the rejected display as a whole. The previous display is no longer retained. *)
      env:=Environ.reset_context globals;sigma:=Evd.from_ctx store.snapshot.universe_state;
      holes:=[];hole_markers:=[];hole_nodes:=[];omitted:=[];displayed_contexts:=[];remaining:=node_limit;charged_placeholders:=0;
      let token=charge()in
      let hole=omit token "node-budget" 0 {root_id;child_path=[]}root.term in
      kernel_surface hole !holes in
    "kernel-constructor","kernel-constructor",text,text,status,Some reason in
  let surface,surface_nonotation,notation,no_notation,status,reason =
    match forced_budget with
    |Some reason->fallback reason "fallback-display-budget"
    |None->try
      typecheck();
      let print mode=with_printing mode(fun()->
        bounded_pp(Printer.pr_econstr_env !env !sigma (EConstr.of_constr truncated))) in
      (try "rocq-notation","rocq-no-notation",print false,print true,"primary-accepted",None
       with Display_budget->fallback "The truncated ordinary printer exceeded the display budget" "fallback-display-budget")
    with Placeholder_typecheck error->fallback error "fallback-placeholder-typecheck" in
  let omitted=List.rev !omitted in
  let display_context=context_ref store {root_id;child_path=[]} in
  let json=`Assoc["schema",`Int 1;"root_id",`String root_id;
    "node_ref",node_json {root_id;child_path=[]};
    "context_roots",`List(List.map node_json(List.rev !displayed_contexts));"surface",`String surface;
    "surface_nonotation",`String surface_nonotation;"goal",`String notation;
    "goal_nonotation",`String no_notation;
    "limits",`Assoc["depth",`Int depth_limit;"nodes",`Int node_limit;"text_bytes_per_mode",`Int text_limit];
    "displayed_nodes",`Int(node_limit - !remaining);
    "complete_sidecar",reference_json store.complete;"context_ref",reference_json display_context;
    "evar_catalog_ref",reference_json store.catalog_ref;"toolchain_ref",reference_json store.toolchain_ref;
    "omitted_subtrees",`List(List.map(fun marker->reference_json marker.marker_ref)omitted);
    "display_holes",`List(List.rev_map(fun (key,name,marker)->
      `Assoc["name",`String name;"display_evar",`Int key;
        "marker_sha256",`String marker.sidecar.sha256;"marker_ref",reference_json marker.marker_ref;
        "scope",`String(if marker.node_ref.root_id=root_id then"term"else"context")])!hole_markers);
    "print_check",`Assoc["status",`String status;"reason",(match reason with None->`Null|Some reason->`String reason)]] in
  if !charged_placeholders<>List.length !hole_nodes then failwith "Uncharged display placeholder";
  {json;notation;no_notation;omitted;charged_placeholders= !charged_placeholders;
    allocated_placeholders=List.length !hole_nodes})
