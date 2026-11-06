From Coq Require Import Lists.List Bool.Bool.
From Ltac2 Require Import Ltac2.
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

Ltac zesu_switch_enabled switch :=
  lazymatch goal with
  | _ : ZesuSwitchDispatchCache ?switches |- _ =>
      zesu_cached_switch switch switches
  | _ => let _ := constr:(_ : switch) in idtac
  end.

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
