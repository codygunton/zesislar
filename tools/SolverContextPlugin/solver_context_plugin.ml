open Ltac_plugin
open Proofview.Notations

let active = Summary.ref ~name:"zesu-solver-context-active" false
let prop_limit = Summary.ref ~name:"zesu-solver-context-props" None
let node_limit = Summary.ref ~name:"zesu-solver-context-nodes" None

let option name read write =
  { Goptions.optstage = Summary.Stage.Interp; optdepr = None;
    optkey = ["Zesu"; "Solver"; name]; optread = read; optwrite = write }

let () =
  Goptions.declare_bool_option (option "Guard" (fun () -> !active) (fun v -> active := v));
  Goptions.declare_int_option (option "PropLimit" (fun () -> !prop_limit) (fun v -> prop_limit := v));
  Goptions.declare_int_option (option "NodeLimit" (fun () -> !node_limit) (fun v -> node_limit := v))

exception Node_limit

let rec count_nodes remaining term =
  if !remaining = 0 then raise Node_limit;
  decr remaining;
  Constr.fold (fun () child -> count_nodes remaining child) () term

let log_refusal site props nodes node_overflow =
  match Sys.getenv_opt "ZESU_SOLVER_REJECTION_DIR" with
  | None -> ()
  | Some directory ->
      if not (Sys.file_exists directory) then Unix.mkdir directory 0o700;
      let path = Filename.concat directory (Printf.sprintf "refusals-%d.jsonl" (Unix.getpid ())) in
      let out = open_out_gen [Open_wronly; Open_creat; Open_append; Open_binary] 0o600 path in
      Fun.protect ~finally:(fun () -> close_out out) (fun () ->
        Yojson.Safe.to_channel out (`Assoc [
          "site", `String site; "prop_facts", `Int props; "kernel_nodes", `Int nodes;
          "nodes_are_lower_bound", `Bool node_overflow;
          "reason", `String "The selected solver input exceeds its limit.";
          "exception_approved", `Bool false]);
        output_char out '\n')

let guard site =
  if not !active then Proofview.tclUNIT () else
  Proofview.tclEVARMAP >>= fun sigma ->
  Proofview.tclENV >>= fun env ->
  Proofview.Unsafe.tclGETGOALS >>= fun goals ->
  let limits = match !prop_limit, !node_limit with
    | Some p, Some n when p > 0 && n > 0 -> Some (p, n)
    | _ -> None in
  match limits with
  | None -> Tacticals.tclFAIL Pp.(str "The solver context policy is not configured.")
  | Some (max_props, max_nodes) ->
      let rejected = ref None in
      List.iter (fun goal ->
        let props = ref 0 and remaining = ref max_nodes and overflow = ref false in
        let visit term =
          if not !overflow then
            try count_nodes remaining (EConstr.Unsafe.to_constr term)
            with Node_limit -> overflow := true in
        let key = Proofview_monad.drop_state goal in
        let info = Evd.find_undefined sigma key in
        let local = Evd.evar_filtered_env env info in
        visit (Evd.evar_concl info);
        List.iter (fun declaration ->
          let module D = Context.Named.Declaration in
          let typ = D.get_type declaration in
          (match Retyping.get_sort_family_of local sigma typ with
           | Sorts.InProp -> incr props | _ -> ());
          visit typ;
          match D.get_value declaration with None -> () | Some value -> visit value)
          (Evd.evar_filtered_context info);
        if !props > max_props || !overflow then (
          let nodes = if !overflow then max_nodes + 1 else max_nodes - !remaining in
          log_refusal site !props nodes !overflow;
          if !rejected = None then rejected := Some (!props, nodes))) goals;
      match !rejected with
      | None -> Proofview.tclUNIT ()
      | Some (props, nodes) ->
          Tacticals.tclFAIL Pp.(str "Solver context refused at " ++ str site ++
            str ": Prop facts=" ++ int props ++ str ", kernel nodes=" ++ int nodes)

let install plugin tactic =
  let name = { Tacexpr.mltac_plugin = plugin; mltac_tactic = tactic } in
  let rec entries index found =
    try
      let original = Tacenv.interp_ml_tactic
        { Tacexpr.mltac_name = name; mltac_index = index } in
      entries (index + 1) (original :: found)
    with error when CErrors.noncritical error -> List.rev found in
  let originals = entries 0 [] in
  if originals = [] then
    CErrors.user_err Pp.(str "Missing pinned solver backend: " ++ str plugin ++ str "/" ++ str tactic);
  let wrapped = Array.of_list (List.mapi (fun index original args ist ->
    let site = Printf.sprintf "backend.%s.%s.%d" plugin tactic index in
    guard site >>= fun () -> original args ist) originals) in
  Tacenv.register_ml_tactic ~overwrite:true name wrapped

let () =
  List.iter (fun (plugin, tactic) -> install plugin tactic)
    ["coq-core.plugins.micromega", "Lia";
     "coq-core.plugins.micromega", "Nia";
     "coq-core.plugins.ring", "ring_lookup";
     "coq-core.plugins.zify", "ITER";
     "coq-core.plugins.zify", "TRANS"]
