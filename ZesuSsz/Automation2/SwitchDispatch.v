From Coq Require Import Lists.List Bool.Bool.
From Ltac2 Require Import Ltac2.
Declare ML Module "zesu-signature-gates.plugin".
Set Default Proof Mode "Classic".

Class ZesuStepSwitchDispatch : Prop := {}.

(* This marker contains tactic data. It is not a typeclass instance. *)
Inductive ZesuSwitchDispatchCache (switches : list (Prop * bool)) : Prop :=
  ZesuSwitchDispatchCached.

(* Continuations carry resolved terms across Ltac's tactical branches. *)
Ltac zesu_resolve_switches switches continuation :=
  lazymatch switches with
  | nil => continuation constr:(@nil (Prop * bool))
  | ?switch :: ?rest =>
      tryif let _ := constr:(_ : switch) in idtac
      then zesu_resolve_switches rest ltac:(fun resolved =>
        continuation constr:((switch, true) :: resolved))
      else zesu_resolve_switches rest ltac:(fun resolved =>
        continuation constr:((switch, false) :: resolved))
  end.

Ltac zesu_cached_switch switch switches :=
  lazymatch switches with
  | nil => let _ := constr:(_ : switch) in idtac
  | (?candidate, ?enabled) :: ?rest =>
      tryif constr_eq switch candidate
      then lazymatch enabled with true => idtac | false => fail 0 end
      else zesu_cached_switch switch rest
  end.

Ltac zesu_switch_enabled_unmemoized switch :=
  lazymatch goal with
  | _ : ZesuSwitchDispatchCache ?switches |- _ =>
      zesu_cached_switch switch switches
  | _ => let _ := constr:(_ : switch) in idtac
  end.

(* Switch memo. Without a switch table in the context, every switch lookup is
   an instance search in the proof context: about 2 ms, some 24 times per
   pass-loop step. Inside `zesu_switch_memo_scope` (one zesu_run), the answer
   of the first search for a switch is reused for later lookups of the same
   switch. Same decisions: the switch instances are global constants and the
   global environment does not change during a proof; the only local change
   that can turn a switch on, a hypothesis that concludes in it, makes the
   lookup search again (so a local override still wins), and so does a switch
   table in the context. The scope empties the memo on entry and on exit
   (success or failure); outside it the memo is never used. The memo lives in
   the gates plugin because Ltac2 has no global mutable state. *)
Ltac2 @ external zesu_switch_memo_scope_set : bool -> unit :=
  "zesu-signature-gates.plugin" "switch_memo_scope".
(* 0: no memo; 1: enabled; 2: disabled; 3: not yet searched. *)
Ltac2 @ external zesu_switch_memo_lookup : constr -> constr -> int :=
  "zesu-signature-gates.plugin" "switch_memo_lookup".
Ltac2 @ external zesu_switch_memo_record : constr -> bool -> unit :=
  "zesu-signature-gates.plugin" "switch_memo_record".

(* The table marker is a global reference: no elaboration per lookup. *)
Ltac2 zesu_switch_memo_enabled (switch : constr) (unmemoized : Ltac1.t) : unit :=
  Control.enter (fun () =>
    let state := zesu_switch_memo_lookup
      (Env.instantiate reference:(ZesuSwitchDispatchCache)) switch in
    if Int.equal state 1 then ()
    else if Int.equal state 2 then Control.zero (Tactic_failure None)
    else if Int.equal state 3 then
      match Control.case (fun () => Ltac1.run unmemoized) with
      | Val _ => zesu_switch_memo_record switch true
      | Err error => zesu_switch_memo_record switch false; Control.zero error
      end
    else Ltac1.run unmemoized).

Ltac2 zesu_switch_memo_run (tactic : Ltac1.t) : unit :=
  zesu_switch_memo_scope_set true;
  Control.plus (fun () => Ltac1.run tactic; zesu_switch_memo_scope_set false)
    (fun error => zesu_switch_memo_scope_set false; Control.zero error).

Ltac zesu_switch_memo_scope tactic :=
  let scope := ltac2:(tactic |- zesu_switch_memo_run tactic) in
  scope tactic.

Ltac zesu_switch_enabled switch :=
  let lookup := ltac2:(switch unmemoized |-
    zesu_switch_memo_enabled (Option.get (Ltac1.to_constr switch)) unmemoized) in
  lookup switch ltac:(idtac; zesu_switch_enabled_unmemoized switch).

(* Count surviving active goals outside the proof context.
   Scoped unshelve places new shelf goals before the active suffix. *)
Ltac2 rec zesu_active_cache_cleanup (count : int) (clean : unit -> unit) :=
  if Int.equal count 0 then []
  else clean :: zesu_active_cache_cleanup (Int.sub count 1) clean.

Ltac2 zesu_cleanup_search_goals (cache : Ltac1.t) (tactic : Ltac1.t) :=
  let count := { contents := 0 } in
  let run := Ltac1.lambda (fun noop =>
    Ltac1.apply tactic [Ltac1.of_constr constr:(tt)] Ltac1.run;
    count.(contents) := 0;
    Control.enter (fun () => count.(contents) := Int.add (count.(contents)) 1);
    noop) in
  ltac1:(run |- unshelve (run ltac:(idtac))) run;
  let clean := fun () =>
    ltac1:(cache |-
      tryif let value := type of cache in idtac
      then clear cache
      else idtac) cache in
  Control.extend [] (fun () => clean (); Control.shelve ())
    (zesu_active_cache_cleanup (count.(contents)) clean).

Ltac zesu_scope_switch_table switches tactic :=
  let cache := fresh "HswitchDispatch" in
  assert (cache : ZesuSwitchDispatchCache switches) by constructor;
  let bridge := ltac2:(cache tactic |- zesu_cleanup_search_goals cache tactic) in
  bridge cache tactic.

Ltac zesu_with_switches switches tactic :=
  zesu_resolve_switches switches ltac:(fun resolved =>
    zesu_scope_switch_table resolved tactic).

Ltac zesu_dispatch_search switches tactic :=
  tryif let _ := constr:(_ : ZesuStepSwitchDispatch) in idtac
  then zesu_with_switches switches tactic
  else lazymatch goal with
    | _ : ZesuSwitchDispatchCache _ |- _ =>
        (* A nested OFF search masks the outer search's table. *)
        zesu_scope_switch_table constr:(@nil (Prop * bool)) tactic
    | _ => tactic tt
    end.
