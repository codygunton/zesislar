open Names
open Kernel_store
let ()=match Array.to_list Sys.argv with
|[_;directory;toolchain_path]->
  Chunks.mkdir directory;
  let toolchain_ref=reference directory toolchain_path in
  let binder=Context.make_annot(Name(Id.of_string "x"))Sorts.Relevant in
  let p=Constr.mkVar(Id.of_string "P") in
  let f=Constr.mkVar(Id.of_string "f") in
  let make_named name typ=Context.Named.Declaration.LocalAssum(Context.make_annot(Id.of_string name)Sorts.Relevant,typ) in
  let context=[make_named "f" (Constr.mkProd(binder,Constr.mkProp,Constr.mkProd(binder,Constr.mkProp,Constr.mkProp)));make_named "P" Constr.mkProp] in
  let dag=ref p in for _=1 to 40 do dag:=Constr.mkApp(f,[|!dag;!dag|])done;
  let deep=ref(Constr.mkRel 1)in for _=1 to 1000 do deep:=Constr.mkLambda(binder,Constr.mkProp,!deep)done;
  let evar key=Constr.mkEvar(Evar.unsafe_of_int key,SList.empty)in
  let root root_id term named={root_id;term;named;relative=[]}in
  let huge=Id.of_string("wide"^String.make 1100000 'x')in
  let huge_context=[Context.Named.Declaration.LocalAssum(Context.make_annot huge Sorts.Relevant,Constr.mkProp)]in
  let rec tree depth=if depth=0 then p else Constr.mkApp(f,[|tree(depth-1);tree(depth-1)|])in
  let sibling_term=Constr.mkApp(f,[|tree 14;p|])in
  let context_type()=let term=ref Constr.mkProp in
    for _=1 to 100 do term:=Constr.mkProd(binder,Constr.mkProp,!term)done;!term in
  let bounded_context=List.init 200(fun n->make_named("context"^string_of_int n)(context_type()))in
  let oversized_context=List.init 20001(fun n->make_named("large"^string_of_int n)Constr.mkProp)in
  let roots=[root "small" (Constr.mkProd(binder,Constr.mkProp,Constr.mkRel 1))[];
    root "shared" !dag context;root "deep" !deep [];
    root "wide" (Constr.mkApp(f,Array.make 100000 p))context;
    root "undefined" (evar 101)[];root "defined" (evar 102)[];
    root "printer-budget" (Constr.mkVar huge)huge_context;
    root "sibling-budget" sibling_term context;
    root "context-budget" Constr.mkProp bounded_context;
    root "oversized-context" Constr.mkProp oversized_context]in
  let catalog=[{key=101;name=Some "source";defined=false;conclusion=Some Constr.mkProp;
    body=None;context=[];filter=[];candidates=None;relevance=Sorts.Relevant};
    {key=102;name=None;defined=true;conclusion=None;body=Some(evar 101);
    context=[];filter=[];candidates=None;relevance=Sorts.Relevant}]in
  let a n=Constr.mkVar(Id.of_string("child"^string_of_int n))in
  let ind=MutInd.make2(ModPath.MPfile DirPath.empty)(Label.make "SyntheticCase")in
  let info={Constr.ci_ind=(ind,0);ci_npar=1;ci_cstr_ndecls=[|1|];ci_cstr_nargs=[|1|];
    ci_pp_info={Constr.ind_tags=[];cstr_tags=[|[true]|];style=Constr.RegularStyle}}in
  let path_roots=[
    root "paths/prod" (Constr.mkProd(binder,a 0,a 1))[];
    root "paths/lambda" (Constr.mkLambda(binder,a 0,a 1))[];
    root "paths/let" (Constr.mkLetIn(binder,a 0,a 1,a 2))[];
    root "paths/app" (Constr.mkApp(a 0,[|a 1;a 2|]))[];
    root "paths/case" (Constr.mkCase(info,UVars.Instance.empty,[|a 0|],(([|binder|],a 1),Sorts.Relevant),
      Constr.CaseInvert{indices=[|a 2|]},a 3,[|([|binder|],a 4)|]))[];
    root "paths/fix" (Constr.mkFix(([|0|],0),([|binder|],[|a 0|],[|a 1|])))[];
    root "paths/cofix" (Constr.mkCoFix(0,([|binder|],[|a 0|],[|a 1|])))[];
    root "paths/array" (Constr.mkArray(UVars.Instance.empty,[|a 0;a 1|],a 2,a 3))[]]in
  List.iter(fun(root:root)->
    let expected=children root.term in
    ignore(map_indexed(fun index term->if List.nth expected index != term then failwith "Canonical child mapping mismatch";term)root.term))path_roots;
  let catalog_roots=List.concat_map(fun entry->
    let make label term={root_id=Printf.sprintf "evar/%d/%s"entry.key label;term;named=entry.context;relative=[]}in
    List.filter_map(fun(label,term)->Option.map(make label)term)["conclusion",entry.conclusion;"body",entry.body] @
    (match entry.candidates with None->[]|Some terms->List.mapi(fun index term->make("candidate/"^string_of_int index)term)terms))catalog in
  let snapshot={schema=1;magic="p0-bounded-kernel-snapshot";toolchain_hash=toolchain_ref.sha256;
    roots=roots@path_roots@catalog_roots;catalog;universe_state=UState.empty;goals=[101];shelf=[];given_up=[];fresh_counter=0}in
  let store=create ~evidence_root:directory ~directory:"kernel" ~toolchain_ref snapshot in
  let nodes=validate snapshot toolchain_ref.sha256 in
  let counter()=Summary.Interp.project_from_summary(Summary.Interp.freeze_summaries())Evd.evar_counter_summary_tag in
  let before=counter()in
  let results=List.map(fun(root:root)->
    let display=Kernel_display.render store Environ.empty_env root.root_id in
    if counter()<>before then failwith "Display changed the fresh counter";
    let ref_=write_json directory ("display-"^root.root_id^".json")display.json in
    root.root_id,display,ref_)roots in
  let markers=List.concat_map(fun(_,display,_)->display.Kernel_display.omitted)results in
  let path_markers=List.concat_map(fun(root:root)->List.mapi(fun index child->
    marker store ~reason:"node-budget" ~depth:1 ~node:{root_id=root.root_id;child_path=[index]}child)(children root.term))path_roots in
  let markers=markers@path_markers in
  let context_ref=write_json directory "root-context.json" (context_json store {root_id="small";child_path=[]})in
  let plan=write_json directory "PLAN.json" (`Assoc["schema",`Int 1;
    "complete_sidecar",reference_json store.complete;"evar_catalog_ref",reference_json store.catalog_ref;
    "context_ref",reference_json context_ref;"toolchain_ref",reference_json toolchain_ref;
    "markers",`List(List.map(fun marker->reference_json marker.marker_ref)markers);
    "reader",(Yojson.Safe.from_file(Filename.concat directory "READER.json"));
    "displays",`List(List.map(fun(name,display,ref_)->`Assoc["display_ref",reference_json ref_;
       "root_id",`String name;"node_ref",node_json {root_id=name;child_path=[]};
       "context_ref",(match display.Kernel_display.json with `Assoc fields->List.assoc "context_ref" fields|_->assert false)])results);
    "receipt_prefix",`String "reload"] )in
  print_endline(Yojson.Safe.to_string(`Assoc["schema",`Int 1;"unique_nodes",`Int nodes;
    "plan",reference_json plan;"fresh_counter_unchanged",`Bool true;
    "displays",`List(List.map(fun(name,display,ref_)->`Assoc["root",`String name;
      "record",reference_json ref_;"markers",`Int(List.length display.Kernel_display.omitted);
      "charged_placeholders",`Int display.Kernel_display.charged_placeholders;
      "allocated_placeholders",`Int display.Kernel_display.allocated_placeholders])results)]))
|_->failwith "Usage: kernel_control ROOT TOOLCHAIN_RELATIVE_PATH"
