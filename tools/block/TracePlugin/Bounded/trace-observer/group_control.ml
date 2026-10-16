let ()=match Array.to_list Sys.argv with
|[_;root;mode]->
  let env=Environ.empty_env in
  let named=Environ.named_context_val env in
  let new_goal sigma=Evd.new_pure_evar named sigma EConstr.type1 in
  let sigma,first=new_goal Evd.empty in
  let sigma,peer=new_goal sigma in
  let sigma,shelved=new_goal sigma in
  let sigma,given=new_goal sigma in
  let sigma=Evd.shelve sigma [shelved]in
  let sigma=Evd.give_up given sigma in
  let sigma,goals=match mode with
    |"mixed"->Evd.define first EConstr.mkProp sigma,[first;peer;first]
    |"defined"->
        let sigma=List.fold_left(fun sigma key->Evd.define key EConstr.mkProp sigma)sigma [first;peer;shelved;given]in
        sigma,[first;peer;first]
    |"shelf"->Evd.define shelved EConstr.mkProp sigma,[first;peer]
    |"given-up"->Evd.define given EConstr.mkProp sigma,[first;peer]
    |_->failwith "Unsupported group case"in
  let counter()=Summary.Interp.project_from_summary(Summary.Interp.freeze_summaries())Evd.evar_counter_summary_tag in
  let before=counter()in
  let sigma_bytes=Marshal.to_string sigma []in
  let writer=Trace_block_chunks.create ~evidence_root:root ~relative_directory:"chunks" ~logical_event:"group-control/capture"in
  Kernel_capture.emit ~evidence_root:root ~directory:"kernel" ~number:1 ~include_proof:false writer env sigma goals before;
  let capture=Trace_block_chunks.finish writer in
  if sigma_bytes<>Marshal.to_string sigma [] || before<>counter()then failwith "Capture changed its source state";
  let result=`Assoc["capture",capture;"mode",`String mode;"unchanged_sigma_bytes",`Bool true;
    "unchanged_fresh_counter",`Bool true;"expected_goals",`List(List.map(fun key->`Int(Evar.repr key))goals);
    "expected_shelf",`List(List.map(fun key->`Int(Evar.repr key))(Evd.shelf sigma));
    "expected_given_up",`List(List.map(fun key->`Int(Evar.repr key))(Evar.Set.elements(Evd.given_up sigma)))]in
  print_endline(Yojson.Safe.to_string result)
|_->failwith "Usage: group_control ROOT MODE"
