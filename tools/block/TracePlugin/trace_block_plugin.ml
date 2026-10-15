open Names
open Ltac2_plugin
open Proofview.Notations

let sequence = ref 0
let invocation = ref 0
let trial_depth = ref 0
let active_invocations = ref []
let active_clause = ref None

let current_invocation () =
  match !active_invocations with [] -> `Null | number :: _ -> `Int number

let enter_invocation number = active_invocations := number :: !active_invocations
let leave_invocation number =
  match !active_invocations with
  | current :: rest when current = number -> active_invocations := rest
  | _ -> CErrors.user_err Pp.(str "The observer invocation stack is inconsistent")

let json_string value = `String value
let json_option f = function None -> `Null | Some value -> f value
let json_list f values = `List (List.map f values)

let render value =
  let buffer = Buffer.create 4096 in
  let formatter = Format.formatter_of_buffer buffer in
  Format.pp_set_margin formatter 1000000;
  Format.pp_set_max_boxes formatter max_int;
  Pp.pp_with formatter value;
  Format.pp_print_flush formatter ();
  Buffer.contents buffer

let output value =
  match Sys.getenv_opt "ZESU_TRACE_EVENT_DIR" with
  | None -> CErrors.user_err Pp.(str "The trace event directory is unavailable")
  | Some root ->
      let directory = Filename.concat root (Printf.sprintf "process-%d" (Unix.getpid ())) in
      if not (Sys.file_exists directory) then Unix.mkdir directory 0o700;
      incr sequence;
      let path = Filename.concat directory (Printf.sprintf "event-%08d.json" !sequence) in
      let channel = open_out_gen [Open_wronly; Open_creat; Open_excl; Open_binary] 0o600 path in
      Fun.protect ~finally:(fun () -> close_out channel)
        (fun () -> Yojson.Safe.to_channel channel value; output_char channel '\n')

let effect callback = Proofview.tclLIFT (Proofview.NonLogical.make callback)

let () =
  ignore (Feedback.add_feeder (fun feedback ->
    match Sys.getenv_opt "ZESU_TRACE_EVENT_DIR", feedback.Feedback.contents with
    | Some _, Feedback.Message (level, _, message) ->
        let level = match level with
          | Feedback.Debug -> "debug" | Feedback.Info -> "info"
          | Feedback.Notice -> "notice" | Feedback.Warning -> "warning"
          | Feedback.Error -> "error" in
        output (`Assoc ["kind", `String "feedback"; "level", `String level;
          "trial", `Bool (!trial_depth > 0);
          "invocation", current_invocation ();
          "clause", (match !active_clause with None -> `Null | Some name -> `String name);
          "message", `String (render message)])
    | _ -> ()))

let with_printing no_notation callback =
  let references =
    [Constrextern.print_no_symbol, no_notation;
     Constrextern.print_implicits, no_notation;
     Constrextern.print_coercions, no_notation;
     Constrextern.print_universes, no_notation;
     Constrextern.print_projections, false;
     Detyping.print_evar_arguments, true] in
  let old = List.map (fun (reference, _) -> reference, !reference) references in
  let depth_key = ["Printing"; "Depth"] in
  let depth = match Goptions.get_option_value depth_key with
    | Some get -> get ()
    | None -> CErrors.user_err Pp.(str "Printing Depth is unavailable") in
  List.iter (fun (reference, value) -> reference := value) references;
  Goptions.set_int_option_value depth_key (Some 10000);
  Fun.protect
    ~finally:(fun () ->
      List.iter (fun (reference, value) -> reference := value) old;
      match depth with
      | Goptions.IntValue value -> Goptions.set_int_option_value depth_key value
      | _ -> CErrors.user_err Pp.(str "Printing Depth has an unexpected type"))
    callback

let key_json key = `Int (Evar.repr key)

let context_json env sigma context =
  let module Decl = Context.Named.Declaration in
  json_list (fun declaration ->
    `Assoc ["names", `List [`String (Id.to_string (Decl.get_id declaration))];
            "type", `String (render (Printer.pr_econstr_env env sigma (Decl.get_type declaration)));
            "body", json_option (fun value ->
              `String (render (Printer.pr_econstr_env env sigma value)))
              (Decl.get_value declaration)])
    (List.rev context)

let goal_json env sigma key =
  let info = Evd.find_undefined sigma key in
  let local = Evd.evar_filtered_env env info in
  `Assoc ["evar", key_json key;
          "name", json_option (fun value -> `String (Id.to_string value))
            (Evd.evar_ident key sigma);
          "conclusion", `String (render (Printer.pr_econstr_env local sigma (Evd.evar_concl info)));
          "hyps", context_json local sigma (Evd.evar_filtered_context info)]

let evar_json env sigma key (Evd.EvarInfo info) =
  let local = Evd.evar_env env info in
  let common =
    ["evar", key_json key;
     "name", json_option (fun value -> `String (Id.to_string value))
       (Evd.evar_ident key sigma);
     "hyps", context_json local sigma (Evd.evar_context info);
     "filter", json_list (fun value -> `Bool value) (Evd.Filter.repr (Evd.evar_filter info)
       |> Stdlib.Option.value ~default:(List.map (fun _ -> true) (Evd.evar_context info)))] in
  match Evd.evar_body info with
  | Evd.Evar_empty ->
      `Assoc (common @ ["defined", `Bool false;
        "type", `String (render (Printer.pr_econstr_env local sigma (Evd.evar_concl info)));
        "body", `Null;
        "candidates", json_option (json_list (fun term ->
          `String (render (Printer.pr_econstr_env local sigma term)))) (Evd.evar_candidates info)])
  | Evd.Evar_defined body ->
      `Assoc (common @ ["defined", `Bool true;
        "body", `String (render (Printer.pr_econstr_env local sigma body));
        "type", `String (render (Printer.pr_econstr_env local sigma
          (Retyping.get_type_of local sigma body)));
        "type_source", `String "Retyping of the defined body; Evd erases its former conclusion."])

let snapshot env sigma goals =
  let summaries = Summary.Interp.freeze_summaries () in
  let counter = Summary.Interp.project_from_summary summaries Evd.evar_counter_summary_tag in
  let goals = List.filter_map (fun goal -> Evarutil.advance sigma goal) goals in
  let shelf = List.filter_map (Evarutil.advance sigma) (Evd.shelf sigma) in
  let given_up = Evar.Set.elements (Evd.given_up sigma) in
  let evars = Evd.fold (fun key info entries -> (key, info) :: entries) sigma [] in
  let evars = List.sort (fun (left, _) (right, _) -> Evar.compare left right) evars in
  let mode no_notation = with_printing no_notation (fun () ->
    `Assoc ["goals", json_list (goal_json env sigma) goals;
            "shelf", json_list (goal_json env sigma) shelf;
            "given_up", json_list (goal_json env sigma) given_up;
            "hidden_stack", `Assoc ["availability", `String "unavailable";
              "reason", `String "Proofview keeps nested focus frames in tactic continuations."];
            "evars", json_list (fun (key, info) -> evar_json env sigma key info) evars;
            "show_existentials", `String (render (Printer.pr_evars_int sigma
               ~shelf ~given_up 1 (Evd.undefined_map sigma)))]) in
  `Assoc ["notation", mode false; "no_notation", mode true;
          "fresh_evar_counter", `Int counter;
          "printer_settings", `Assoc [
            "notations", `Bool (not !(Constrextern.print_no_symbol));
            "implicits", `Bool !(Constrextern.print_implicits);
            "universes", `Bool !(Constrextern.print_universes);
            "evar_arguments", `Bool !(Detyping.print_evar_arguments)];
          "printing_depth", `Int 10000]

let capture kind name number additional =
  Proofview.tclENV >>= fun env ->
  Proofview.tclEVARMAP >>= fun sigma ->
  Proofview.Unsafe.tclGETGOALS >>= fun goals ->
  let goals = List.map Proofview_monad.drop_state goals in
  effect (fun () -> output (`Assoc
    (["kind", `String kind; "rule", `String name; "invocation", `Int number;
      "trial", `Bool (!trial_depth > 0); "observer_invocation", current_invocation ();
      "capture", snapshot env sigma goals] @ additional)))

let read_live =
  Proofview.tclENV >>= fun env ->
  Proofview.tclEVARMAP >>= fun sigma ->
  Proofview.Unsafe.tclGETGOALS >>= fun goals ->
  Proofview.tclUNIT (snapshot env sigma (List.map Proofview_monad.drop_state goals))

exception Trace_trial_finished

let trial name number clause callback =
  (* The forced failure restores the exact entry state before the handler runs. *)
  read_live >>= fun before ->
  effect (fun () -> Summary.Interp.freeze_summaries (), Summary.Synterp.freeze_summaries ())
    >>= fun (interp, synterp) ->
  effect (fun () ->
    incr trial_depth; active_clause := Some clause; enter_invocation number) <*>
  Proofview.tclOR
    (Proofview.tclONCE (Tac2ffi.app_fun1 callback Tac2ffi.unit Tac2ffi.unit ()) >>= fun () ->
     capture "hand-accepted" name number ["clause", `String clause] <*>
     Proofview.tclZERO Trace_trial_finished)
    (fun (error, _) ->
      effect (fun () ->
        decr trial_depth; active_clause := None; leave_invocation number;
        Summary.Synterp.unfreeze_summaries synterp;
        Summary.Interp.unfreeze_summaries interp) <*>
      read_live >>= fun retained ->
      capture "hand-rollback" name number
        ["clause", `String clause; "exact", `Bool (before = retained)] <*>
      if before <> retained then
        Tacticals.tclFAIL Pp.(str "The hand trial changed its retained entry state")
      else match error with
        | Trace_trial_finished -> Proofview.tclUNIT ()
        | _ -> capture "hand-refused" name number
            ["clause", `String clause; "refusal", `String (render (CErrors.print error))])

let rec observe_results name number tactic =
  effect (fun () -> enter_invocation number) <*>
  Proofview.tclCASE tactic >>= function
  | Proofview.Fail (error, info) ->
      effect (fun () -> leave_invocation number) <*>
      capture "native-exhausted" name number
        ["refusal", `String (render (CErrors.print error))] <*>
      Proofview.tclZERO ~info error
  | Proofview.Next (value, continuation) ->
      effect (fun () -> leave_invocation number) <*>
      capture "native-local-success" name number
        ["parent_branch_survival", `String "not-established"] <*>
      Proofview.tclOR (Proofview.tclUNIT value) (fun error ->
        capture "native-backtracked" name number
          ["refusal", `String (render (CErrors.print (fst error)))] <*>
        observe_results name number (continuation error))

let around name clauses callback =
  if !trial_depth > 0 then Tac2ffi.app_fun1 callback Tac2ffi.unit Tac2ffi.unit ()
  else
    effect (fun () -> incr invocation; !invocation) >>= fun number ->
    capture "native-entry" name number [] <*>
    List.fold_left (fun result (clause, body) ->
      result <*> trial name number clause body) (Proofview.tclUNIT ()) clauses <*>
    trial name number "whole-rule" callback <*>
    observe_results name number (Tac2ffi.app_fun1 callback Tac2ffi.unit Tac2ffi.unit ())

let () =
  let open Tac2externals in
  let callback = Tac2ffi.fun1 Tac2ffi.unit Tac2ffi.unit in
  define { Tac2expr.mltac_plugin = "zesu-signature-gates.trace-observer";
           mltac_tactic = "around" }
    (Tac2ffi.string @-> Tac2ffi.list (Tac2ffi.pair Tac2ffi.string callback) @->
     callback @-> tac Tac2ffi.unit)
    around;
  define { Tac2expr.mltac_plugin = "zesu-signature-gates.trace-observer";
           mltac_tactic = "snapshot" }
    (Tac2ffi.string @-> tac Tac2ffi.unit)
    (fun label -> capture "checkpoint" label 0 [])
