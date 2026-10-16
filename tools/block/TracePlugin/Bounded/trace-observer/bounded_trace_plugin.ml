module Chunks = Trace_block_chunks
open Names
open Ltac2_plugin
open Proofview.Notations

let sequence = ref 0
let selected_feedback_emitted=ref 0
let selected_feedback_omitted=ref 0
let first_feedback_error=ref None
let diagnostic_errors = ref 0
let unrecorded_errors = ref 0
let hand_trials_started = ref 0
let hand_trials_accepted = ref 0
let hand_trials_refused = ref 0
let hand_trials_rolled_back = ref 0
let first_unrecorded_error = ref None
let first_diagnostic_error = ref None
let diagnostic_error phase error =
  incr diagnostic_errors;
  let exact = Printexc.to_string error in
  if !first_diagnostic_error = None then first_diagnostic_error := Some (phase, exact);
  exact
let record_unavailable phase original error =
  incr unrecorded_errors;
  if !first_unrecorded_error = None then
    first_unrecorded_error := Some (phase, original, Printexc.to_string error)
let diagnostic phase callback =
  try callback () with error when CErrors.noncritical error ->
    ignore (diagnostic_error phase error)
let optional_diagnostic phase callback =
  try Some (callback ()) with error when CErrors.noncritical error ->
    ignore (diagnostic_error phase error); None
let diagnostic_status () =
  let pair = function None -> `Null | Some (phase, error) ->
    `Assoc ["phase", `String phase; "error", `String error] in
  let unrecorded = match !first_unrecorded_error with None -> `Null
    | Some (phase, original, error) -> `Assoc ["phase", `String phase;
      "capture_error", `String original; "logging_error", `String error] in
  let raw_budget=Trace_raw_budget.status()in
  let budget_complete=match raw_budget with `Assoc fields->List.assoc "limit_reached"fields=`Bool false|_->true in
  Yojson.Safe.to_string (`Assoc (["schema", `Int 1;
    "complete", `Bool (!diagnostic_errors = 0 && !unrecorded_errors = 0 && budget_complete);
    "diagnostic_errors", `Int !diagnostic_errors;
    "unrecorded_errors", `Int !unrecorded_errors;
    "hand_trials", `Assoc ["started", `Int !hand_trials_started;
      "accepted", `Int !hand_trials_accepted; "refused", `Int !hand_trials_refused;
      "rolled_back", `Int !hand_trials_rolled_back];
    "first_error", pair !first_diagnostic_error;
    "first_unrecorded_error", unrecorded] @ (if raw_budget=`Null then []else[
      "raw_budget",raw_budget;
      "selected_feedback",`Assoc["emitted",`Int !selected_feedback_emitted;
        "omitted",`Int !selected_feedback_omitted;"complete",`Bool(!selected_feedback_omitted=0);
        "first_error",(match !first_feedback_error with None->`Null|Some error->`String error)]])))
let invocation = ref 0
let trial_depth = ref 0
let active_invocations = ref []
let active_clause = ref None
let feedback_counts = Hashtbl.create 8
let full_active () =
  if Trace_raw_budget.configured()=None then List.exists(fun(_,full)->full)!active_invocations
  else match !active_invocations with []->false|(_,full)::_->full
let current_invocation () = match !active_invocations with [] -> `Null | (n, _) :: _ -> `Int n
let enter number full = active_invocations := (number, full) :: !active_invocations
let leave number = match !active_invocations with
  | (current, _) :: rest when current = number -> active_invocations := rest
  | _ -> CErrors.user_err Pp.(str "The observer invocation stack is inconsistent")
let effect callback = Proofview.tclLIFT (Proofview.NonLogical.make callback)
let event_root () = match Sys.getenv_opt "ZESU_TRACE_EVENT_DIR" with
  | Some path -> path
  | None -> CErrors.user_err Pp.(str "The trace event directory is unavailable")
let reserve () = incr sequence; !sequence
let envelope number fields =
  let directory = Filename.concat (event_root ()) (Printf.sprintf "process-%d" (Unix.getpid ())) in
  Chunks.mkdir directory;
  let data = Yojson.Safe.to_string (`Assoc (["schema", `Int 2; "sequence", `Int number] @ fields)) ^ "\n" in
  if String.length data > Chunks.physical_limit then
    CErrors.user_err Pp.(str "The serialized observer envelope exceeds 2 MiB");
  let path = Filename.concat directory (Printf.sprintf "event-%08d.json" number) in
  Trace_raw_budget.with_output path(fun channel->output_string channel data)
let payload number field emit =
  Trace_raw_budget.ensure_data();
  let relative_directory = Printf.sprintf "events/process-%d/chunks/event-%08d-%s" (Unix.getpid ()) number field in
  let logical_event = Printf.sprintf "event-%08d/%s" number field in
  let writer = Chunks.create ~evidence_root:(Filename.dirname (event_root ())) ~relative_directory ~logical_event in
  emit writer;
  Chunks.finish writer
let emit fields = diagnostic "counter-envelope" (fun () ->
  if Sys.getenv_opt "ZESU_TRACE_INJECT_LOG_FAILURE" = Some "1" then
    failwith "P0-DIAGNOSTIC-LOG-INJECTED";
  let number = reserve () in envelope number fields)
let identity kind name number = [
  "kind", `String kind; "rule", `String name; "invocation", `Int number;
  "trial", `Bool (!trial_depth > 0); "parent_invocation", current_invocation ()]
let rule name = if String.starts_with ~prefix:"ReturnRoute." name then "ReturnRoute"
  else if String.starts_with ~prefix:"MemoryAccess." name then "MemoryAccess"
  else if name = "Hooks.zesu_conjunct_head_if_enabled" then "ConjunctMatch" else name
let guard_manifest = lazy (
  match Sys.getenv_opt "ZESU_TRACE_GUARD_MANIFEST" with
  | None -> []
  | Some path ->
      if (Unix.stat path).Unix.st_size > Chunks.physical_limit then
        CErrors.user_err Pp.(str "The guard manifest exceeds 2 MiB");
      match Yojson.Safe.from_file path with
      | `Assoc fields when List.assoc_opt "schema" fields = Some (`Int 2) ->
          (match List.assoc_opt "clients" fields with
           | Some (`Assoc clients) -> List.filter_map (fun (name, entry) ->
               match entry with
               | `Assoc fields ->
                   (match List.assoc_opt "command" fields,
                          List.assoc_opt "sha256" fields,
                          List.assoc_opt "semantics" fields with
                    | Some (`String command), Some (`String hash),
                      Some (`String "switch-independent-discarded")
                      when String.length hash = 64 &&
                        String.for_all (function '0'..'9' | 'a'..'f' -> true | _ -> false) hash &&
                        Chunks.sha256_text command = hash -> Some (name, hash)
                    | _ -> None)
               | _ -> None) clients
           | _ -> [])
      | _ -> [])
let guard_hash name = match optional_diagnostic "guard-manifest" (fun () ->
  List.assoc_opt name (Lazy.force guard_manifest)) with Some hash -> hash | None -> None
let option key = match Goptions.get_option_value key with
  | Some get -> get ()
  | None -> CErrors.user_err Pp.(str "A required observer option is unavailable")
let debug_option () = option ["Typeclasses"; "Debug"; "Verbosity"]
let set_debug value = Goptions.set_int_option_value ["Typeclasses"; "Debug"; "Verbosity"] value
let restore_debug = function
  | Goptions.IntValue value -> set_debug value
  | _ -> CErrors.user_err Pp.(str "The debug option has an unexpected type")
let () = ignore (Feedback.add_feeder (fun feedback ->
  match Sys.getenv_opt "ZESU_TRACE_EVENT_DIR", feedback.Feedback.contents with
  | Some _, Feedback.Message (level, _, message) ->
      let level = match level with Feedback.Debug -> "debug" | Feedback.Info -> "info"
        | Feedback.Notice -> "notice" | Feedback.Warning -> "warning" | Feedback.Error -> "error" in
      if full_active () then (try
        if Sys.getenv_opt "ZESU_TRACE_INJECT_LOG_FAILURE" = Some "1" then
          failwith "P0-DIAGNOSTIC-LOG-INJECTED";
        let number = reserve () in
        let message = payload number "message" (fun writer -> Chunks.pp writer message) in
        envelope number ["kind", `String "feedback"; "level", `String level;
          "trial", `Bool (!trial_depth > 0); "invocation", current_invocation ();
          "clause", (match !active_clause with None -> `Null | Some clause -> `String clause);
          "message", message];
        incr selected_feedback_emitted
       with error when CErrors.noncritical error->
        incr selected_feedback_omitted;
        let exact=diagnostic_error "feedback-output"error in
        if !first_feedback_error=None then first_feedback_error:=Some exact)
      else (
        let count = match Hashtbl.find_opt feedback_counts level with None -> 0 | Some n -> n in
        Hashtbl.replace feedback_counts level (count + 1))
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


let fresh_counter () =
  let summaries=Summary.Interp.freeze_summaries()in
  Summary.Interp.project_from_summary summaries Evd.evar_counter_summary_tag
let native_captures=Hashtbl.create 16
let capture kind name invocation additional =
  Proofview.tclENV >>= fun env ->
  Proofview.tclEVARMAP >>= fun sigma ->
  Proofview.Unsafe.tclGETGOALS >>= fun goals ->
  let goals=List.map Proofview_monad.drop_state goals in
  effect(fun()->
    try
      if Sys.getenv_opt "ZESU_TRACE_INJECT_CAPTURE_FAILURE"=Some"1"then
        failwith "P0-CAPTURE-SERIALIZATION-INJECTED";
      let number=reserve()in
      let evidence_root=Filename.dirname(event_root())in
      let directory=Printf.sprintf "kernel/process-%d/event-%08d"(Unix.getpid())number in
      let captured=payload number "capture"(fun writer->
        Kernel_capture.emit ~evidence_root ~directory ~number
          ~include_proof:(kind="checkpoint" && name="residual")writer env sigma goals(fresh_counter()))in
      envelope number(identity kind name invocation@["capture",captured]@additional);
      if kind="native-entry"then
        Hashtbl.replace native_captures invocation(number,captured,env,sigma,goals,fresh_counter())
    with error when CErrors.noncritical error ->
      let exact_error=diagnostic_error "capture-serialization" error in
      (try
        if Sys.getenv_opt "ZESU_TRACE_INJECT_ERROR_RECORD_FAILURE"=Some"1" then
          failwith "P0-CAPTURE-ERROR-RECORD-INJECTED";
        let number=reserve()in
        let error_reference=payload number "capture-error"(fun writer->Chunks.string writer exact_error)in
        envelope number(identity "capture-error"name invocation@[
          "captured_kind",`String kind;"phase",`String "capture-serialization";
          "complete",`Bool false;"error",error_reference]@additional)
       with logging_error when CErrors.noncritical logging_error ->
        record_unavailable "capture-error-output" exact_error logging_error))
let read_live =
  Proofview.tclEVARMAP >>= fun sigma ->
  Proofview.Unsafe.tclGETGOALS >>= fun goals ->
  effect (fun () -> sigma, List.map Proofview_monad.drop_state goals,
    Evd.shelf sigma, Evd.given_up sigma, fresh_counter (),
    (!(Constrextern.print_no_symbol), !(Constrextern.print_implicits),
     !(Constrextern.print_coercions), !(Constrextern.print_universes),
     !(Constrextern.print_projections), !(Detyping.print_evar_arguments),
     option ["Printing"; "Depth"], debug_option ()))
let same_live (sigma, goals, shelf, given_up, counter, printing)
    (sigma', goals', shelf', given_up', counter', printing') =
  sigma == sigma' && goals = goals' && shelf = shelf' &&
  Evar.Set.equal given_up given_up' && counter = counter' && printing = printing'
let rollback_capture name number clause before after before_env after_env =
  if not(same_live before after) || before_env != after_env then
    Tacticals.tclFAIL Pp.(str "The hand trial changed its retained entry state")
  else if Trace_raw_budget.configured()=None then
    capture "hand-rollback"name number["clause",`String clause;"exact",`Bool true]
  else
    let sigma,goals,shelf,given_up,fresh,_=before in
    match Hashtbl.find_opt native_captures number with
    |Some(source_sequence,captured,source_env,source_sigma,source_goals,source_fresh)
      when source_env==before_env && source_sigma==sigma && source_goals=goals &&
        Evd.shelf source_sigma=shelf && Evar.Set.equal(Evd.given_up source_sigma)given_up && source_fresh=fresh ->
      effect(fun()->diagnostic "rollback-reference-output"(fun()->
        let ordinal=reserve()in
        let relative=Printf.sprintf "events/process-%d/event-%08d.json"(Unix.getpid())source_sequence in
        let event=Kernel_store.reference(Filename.dirname(event_root()))relative in
        envelope ordinal(identity "hand-rollback"name number@[
          "clause",`String clause;"exact",`Bool true;
          "capture_ref",`Assoc["event",Kernel_store.reference_json event;"capture",captured;
            "source_sequence",`Int source_sequence];
          "reuse_check",`Assoc(("kind",`String "discarded-branch-rollback")::
            List.map(fun key->key,`Bool true)["exact";"proofview_backtracked";
              "interp_summary_restored";"synterp_summary_restored";"evd_physical_equal";
              "environment_physical_equal";"ordered_groups_equal";"fresh_counter_equal"])])))
    |_->effect(fun()->ignore(diagnostic_error "rollback-reference-unavailable"
      (Failure "The hand rollback has no matching complete native entry")))
exception Guard_finished of bool
exception Trace_trial_finished
let evaluate_guard callback =
  let module B = Logic_monad.BackState in
  let module N = Logic_monad.NonLogical in
  let computation = B.(get >>= fun state ->
    let pull = N.(make (fun () ->
      B.run (Proofview.UnsafeRepr.repr (Proofview.tclONCE
        (Tac2ffi.app_fun1 callback Tac2ffi.unit Tac2ffi.bool ()))) state)
      >>= fun reified -> B.repr reified) in
    let caught = N.catch pull (fun ((error, _) as original) ->
      if CErrors.noncritical error then N.return (Logic_monad.Nil original)
      else N.raise original) in
    lift caught >>= function
    | Logic_monad.Nil error -> zero error
    | Logic_monad.Cons ((value, state), _) -> set state >>= fun () -> return value) in
  Proofview.UnsafeRepr.make computation
let discarded_guard callback =
  read_live >>= fun before ->
  effect (fun () -> Summary.Interp.freeze_summaries (), Summary.Synterp.freeze_summaries ())
    >>= fun (interp, synterp) ->
  effect (fun () -> incr trial_depth) <*>
  Proofview.tclOR
    (evaluate_guard callback >>= fun value ->
     Proofview.tclZERO (Guard_finished value))
    (fun (error, _) ->
      effect (fun () -> decr trial_depth;
        Summary.Synterp.unfreeze_summaries synterp; Summary.Interp.unfreeze_summaries interp) <*>
      read_live >>= fun after ->
      if not (same_live before after) then
        Tacticals.tclFAIL Pp.(str "The typed guard changed its retained entry state")
      else Proofview.tclUNIT (match error with Guard_finished value -> Some value | _ -> None))
let trial name number clause callback =
  Proofview.tclENV >>= fun before_env ->
  read_live >>= fun before ->
  effect (fun () -> Summary.Interp.freeze_summaries (), Summary.Synterp.freeze_summaries ())
    >>= fun (interp, synterp) ->
  effect (fun () -> incr hand_trials_started; incr trial_depth; active_clause := Some clause; enter number true) <*>
  Proofview.tclOR
    (Proofview.tclONCE (Tac2ffi.app_fun1 callback Tac2ffi.unit Tac2ffi.unit ()) >>= fun () ->
     effect (fun () -> incr hand_trials_accepted) <*>
     capture "hand-accepted" name number ["clause", `String clause] <*>
     Proofview.tclZERO Trace_trial_finished)
    (fun (error, _) ->
      effect (fun () -> decr trial_depth; active_clause := None; leave number;
        Summary.Synterp.unfreeze_summaries synterp; Summary.Interp.unfreeze_summaries interp) <*>
      read_live >>= fun after ->
      Proofview.tclENV >>= fun after_env ->
      rollback_capture name number clause before after before_env after_env <*>
      if not (same_live before after) then
        Tacticals.tclFAIL Pp.(str "The hand trial changed its retained entry state")
      else
        effect (fun () -> incr hand_trials_rolled_back;
          match error with Trace_trial_finished -> () | _ -> incr hand_trials_refused) <*>
        (match error with
      | Trace_trial_finished -> Proofview.tclUNIT ()
      | _ -> effect (fun () -> diagnostic "refusal-output" (fun () ->
          if Sys.getenv_opt "ZESU_TRACE_INJECT_LOG_FAILURE" = Some "1" then
            failwith "P0-DIAGNOSTIC-LOG-INJECTED";
          let ordinal = reserve () in
          let refusal = payload ordinal "refusal" (fun writer -> Chunks.pp writer (CErrors.print error)) in
          envelope ordinal (identity "hand-refused" name number @ ["clause", `String clause; "refusal", refusal])))))
let counter name number hash classification outcome before after =
  Proofview.Unsafe.tclGETGOALS >>= fun goals ->
  effect (fun () -> emit [
    "kind", `String (if outcome = "entry" then "guard-counter" else "branch-counter");
    "trial", `Bool false; "invocation", `Int number;
    "focused_goals", `List (List.map (fun goal -> `Int (Evar.repr (Proofview_monad.drop_state goal))) goals);
    "parent_invocation", current_invocation (); "client", `String name; "rule", `String (rule name);
    "guard_hash", (match hash with None -> `Null | Some value -> `String value);
    "classification", `String classification; "outcome", `String outcome;
    "fresh_evar_before", `Int before; "fresh_evar_after", `Int after])
let rec observe_results name number hash classification full tactic =
  effect (fun () -> let old = debug_option () in let before = fresh_counter () in if full then set_debug (Some 2); enter number full; old, before)
    >>= fun (debug, before) ->
  Proofview.tclCASE tactic >>= function
  | Proofview.Fail (error, info) ->
      effect (fun () -> leave number; restore_debug debug) <*>
      counter name number hash classification "native-exhausted" before (fresh_counter ()) <*>
      Proofview.tclZERO ~info error
  | Proofview.Next (value, continuation) ->
      effect (fun () -> leave number; restore_debug debug) <*>
      counter name number hash classification "native-local-success" before (fresh_counter ()) <*>
      Proofview.tclOR (Proofview.tclUNIT value) (fun error ->
        counter name number hash classification "native-backtracked" before (fresh_counter ()) <*>
        observe_results name number hash classification full (continuation error))
let filtered name guard clauses callback =
  if !trial_depth > 0 then Tac2ffi.app_fun1 callback Tac2ffi.unit Tac2ffi.unit ()
  else
    effect (fun () -> incr invocation; !invocation, fresh_counter (), guard_hash name)
      >>= fun (number, before, hash) ->
    discarded_guard guard >>= fun result ->
    let classification = match hash, result with
      | Some _, Some true -> "actual-trigger" | Some _, Some false -> "non-trigger" | _ -> "unknown" in
    let full = classification = "actual-trigger" in
    counter name number hash classification "entry" before (fresh_counter ()) <*>
    (if full then (
      capture "native-entry" name number [] <*>
      effect (fun () -> let old = debug_option () in set_debug (Some 2); old) >>= fun debug ->
      List.fold_left (fun result (clause, body) -> result <*> trial name number clause body)
        (Proofview.tclUNIT ()) clauses <*>
      trial name number "whole-rule" callback <*>
      effect (fun () -> Hashtbl.remove native_captures number; restore_debug debug)) else Proofview.tclUNIT ()) <*>
    observe_results name number hash classification full (Tac2ffi.app_fun1 callback Tac2ffi.unit Tac2ffi.unit ())
let checkpoint label =
  if label = "residual" then capture "checkpoint" label 0 []
  else effect (fun () -> emit ["kind", `String "checkpoint-counter"; "trial", `Bool (!trial_depth > 0); "label", `String label;
    "invocation", current_invocation (); "literal_pc", `Null;
    "pc_availability", `String "A typed instruction callback must supply the PC."])
let rec positive sigma term =
  let constructor term = match EConstr.kind sigma term with
    | Constr.Construct (((mutind, _), ordinal), _) when
        MutInd.to_string mutind = "Coq.Numbers.BinNums.positive" -> Some ordinal
    | _ -> None in
  match EConstr.kind sigma term with
  | Constr.Construct _ when constructor term = Some 3 -> Some Z.one
  | Constr.App (head, [|argument|]) ->
      (match constructor head, positive sigma argument with
       | Some 1, Some value -> Some Z.(add (mul (of_int 2) value) one)
       | Some 2, Some value -> Some Z.(mul (of_int 2) value)
       | _ -> None)
  | _ -> None
let closed_integer sigma term =
  let constructor term = match EConstr.kind sigma term with
    | Constr.Construct (((mutind, _), ordinal), _) when
        MutInd.to_string mutind = "Coq.Numbers.BinNums.Z" -> Some ordinal
    | _ -> None in
  match EConstr.kind sigma term with
  | Constr.Construct _ when constructor term = Some 1 -> Some Z.zero
  | Constr.App (head, [|argument|]) ->
      (match constructor head, positive sigma argument with
       | Some 2, Some value -> Some value
       | Some 3, Some value -> Some (Z.neg value)
       | _ -> None)
  | _ -> None
let lightweight_checkpoint label pc =
  Proofview.tclEVARMAP >>= fun sigma ->
  Proofview.Unsafe.tclGETGOALS >>= fun goals ->
  effect (fun () ->
    let literal = closed_integer sigma pc in
    emit ["kind", `String "checkpoint-counter"; "trial", `Bool (!trial_depth > 0); "label", `String label;
      "invocation", current_invocation ();
      "focused_goals", `List (List.map (fun goal -> `Int (Evar.repr (Proofview_monad.drop_state goal))) goals);
      "fresh_evar_counter", `Int (fresh_counter ());
      "literal_pc", (match literal with None -> `Null | Some value -> `String (Z.to_string value));
      "pc_availability", `String (match literal with None -> "unavailable" | Some _ -> "closed-literal")])
let () =
  let open Tac2externals in
  define { Tac2expr.mltac_plugin = "p0-bounded-trace.trace-observer"; mltac_tactic = "status" }
    (Tac2ffi.unit @-> tac Tac2ffi.string) (fun () -> effect diagnostic_status);
  define { Tac2expr.mltac_plugin = "p0-bounded-trace.trace-observer"; mltac_tactic = "complete" }
    (Tac2ffi.unit @-> tac Tac2ffi.bool) (fun () -> effect (fun () ->
      let budget=Trace_raw_budget.status()in
      let allowed=match budget with `Assoc fields->List.assoc "limit_reached"fields=`Bool false|_->true in
      !diagnostic_errors = 0 && !unrecorded_errors = 0 && allowed));
  let callback = Tac2ffi.fun1 Tac2ffi.unit Tac2ffi.unit in
  let guard = Tac2ffi.fun1 Tac2ffi.unit Tac2ffi.bool in
  define { Tac2expr.mltac_plugin = "p0-bounded-trace.trace-observer"; mltac_tactic = "filtered" }
    (Tac2ffi.string @-> guard @-> Tac2ffi.list (Tac2ffi.pair Tac2ffi.string callback) @-> callback @-> tac Tac2ffi.unit) filtered;
  define { Tac2expr.mltac_plugin = "p0-bounded-trace.trace-observer"; mltac_tactic = "snapshot" }
    (Tac2ffi.string @-> tac Tac2ffi.unit) checkpoint;
  define { Tac2expr.mltac_plugin = "p0-bounded-trace.trace-observer"; mltac_tactic = "checkpoint" }
    (Tac2ffi.string @-> Tac2ffi.constr @-> tac Tac2ffi.unit) lightweight_checkpoint
