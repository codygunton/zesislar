Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SwitchDispatch.
From Coq Require Import Lists.List Bool.Bool.
Import ListNotations.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Ltac2 fixture_exact_shared () :=
  let goal := Control.goal () in
  match Constr.Unsafe.kind goal with
  | Constr.Unsafe.App _ args =>
      Control.assert_true (Int.equal (Array.length args) 3);
      let witness := Array.get args 1 in
      Control.assert_true (Constr.equal witness (Array.get args 2));
      (match Constr.Unsafe.kind witness with
       | Constr.Unsafe.Evar _ _ => ()
       | _ => Control.throw Assertion_failure end);
      Control.assert_true (Constr.equal goal constr:($witness = $witness))
  | _ => Control.throw Assertion_failure
  end.

Class FixtureSwitch : Prop := {}.
Ltac fixture_disabled :=
  tryif zesu_switch_enabled constr:(FixtureSwitch)
  then fail 0 "The fixture switch is enabled" else idtac.
Ltac fixture_no_marker :=
  tryif match goal with _ : ZesuSwitchDispatchCache _ |- _ => idtac end
  then fail 0 "The cache marker remains" else idtac.

Lemma count_switch_search_isolation : True.
Proof.
  let switches := constr:([FixtureSwitch]) in
  assert (Hdispatch : ZesuStepSwitchDispatch) by constructor;
  zesu_dispatch_search switches ltac:(fun _ => fixture_disabled);
  fixture_no_marker;
  assert (Hlocal : FixtureSwitch) by constructor;
  zesu_dispatch_search switches ltac:(fun _ => zesu_switch_enabled constr:(FixtureSwitch));
  fixture_no_marker;
  clear Hlocal;
  zesu_dispatch_search switches ltac:(fun _ => fixture_disabled);
  fixture_no_marker.
  exact I.
Qed.
Print Assumptions count_switch_search_isolation.

Lemma count_switch_nested_isolation : True.
Proof.
  let switches := constr:([FixtureSwitch]) in
  assert (Hdispatch : ZesuStepSwitchDispatch) by constructor;
  assert (Hlocal : FixtureSwitch) by constructor;
  zesu_dispatch_search switches ltac:(fun _ => 
    zesu_switch_enabled constr:(FixtureSwitch);
    clear Hlocal;
    zesu_dispatch_search switches ltac:(fun _ => fixture_disabled);
    zesu_switch_enabled constr:(FixtureSwitch);
    clear Hdispatch;
    zesu_dispatch_search switches ltac:(fun _ => fixture_disabled);
    zesu_switch_enabled constr:(FixtureSwitch));
  fixture_no_marker.
  exact I.
Qed.
Print Assumptions count_switch_nested_isolation.

Lemma count_switch_search_rollback : True.
Proof.
  assert (Hdispatch : ZesuStepSwitchDispatch) by constructor.
  first [zesu_dispatch_search constr:([FixtureSwitch]) ltac:(fun _ => fail 0) | idtac].
  fixture_no_marker.
  exact I.
Qed.
Print Assumptions count_switch_search_rollback.

Lemma count_switch_off_lookup : True.
Proof.
  fixture_disabled.
  assert (Hlocal : FixtureSwitch) by constructor.
  zesu_dispatch_search constr:([FixtureSwitch]) ltac:(fun _ => zesu_switch_enabled constr:(FixtureSwitch)).
  fixture_no_marker.
  clear Hlocal.
  zesu_dispatch_search constr:([FixtureSwitch]) ltac:(fun _ => fixture_disabled).
  fixture_no_marker.
  exact I.
Qed.
Print Assumptions count_switch_off_lookup.

Lemma count_switch_branch_cleanup : True /\ True.
Proof.
  assert (Hdispatch : ZesuStepSwitchDispatch) by constructor.
  zesu_dispatch_search constr:([FixtureSwitch]) ltac:(fun _ => split).
  all: fixture_no_marker; exact I.
Qed.
Print Assumptions count_switch_branch_cleanup.

Lemma count_switch_shelf_cleanup : True /\ True.
Proof.
  assert (Hdispatch : ZesuStepSwitchDispatch) by constructor.
  zesu_dispatch_search constr:([FixtureSwitch]) ltac:(fun _ => split; [shelve | idtac]).
  all: fixture_no_marker; exact I.
  Unshelve.
  all: fixture_no_marker; exact I.
Qed.
Print Assumptions count_switch_shelf_cleanup.

Ltac fixture_shelve_boundary _ := shelve.

Lemma count_switch_groups_off : 0 = 0 /\ 1 = 1 /\ 2 = 2.
Proof.
  split; [shelve | split].
  1: zesu_run_until fixture_shelve_boundary.
  all: match goal with |- ?g => idtac "OFF-ACTIVE" g end.
  all: fixture_no_marker; reflexivity.
  Unshelve.
  all: match goal with |- ?g => idtac "OFF-SHELF" g end.
  all: fixture_no_marker; reflexivity.
Qed.
Print Assumptions count_switch_groups_off.

Lemma count_switch_groups_on : 0 = 0 /\ 1 = 1 /\ 2 = 2.
Proof.
  assert (Hdispatch : ZesuStepSwitchDispatch) by constructor.
  split; [shelve | split].
  1: zesu_run_until fixture_shelve_boundary.
  all: match goal with |- ?g => idtac "ON-ACTIVE" g end.
  all: fixture_no_marker; reflexivity.
  Unshelve.
  all: match goal with |- ?g => idtac "ON-SHELF" g end.
  all: fixture_no_marker; reflexivity.
Qed.
Print Assumptions count_switch_groups_on.

Lemma count_shared_off : exists n : nat, n = n.
Proof.
  zesu_dispatch_search constr:(@nil Prop) ltac:(fun _ => unshelve eexists).
  1: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(nat))).
  2: ltac2:(fixture_exact_shared ()).
  all: fixture_no_marker.
  1: exact O.
  all: reflexivity.
Qed.
Print Assumptions count_shared_off.

Lemma count_shared_on : exists n : nat, n = n.
Proof.
  assert (Hdispatch : ZesuStepSwitchDispatch) by constructor.
  zesu_dispatch_search constr:(@nil Prop) ltac:(fun _ => unshelve eexists).
  1: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(nat))).
  2: ltac2:(fixture_exact_shared ()).
  all: fixture_no_marker.
  1: exact O.
  all: reflexivity.
Qed.
Print Assumptions count_shared_on.

Lemma count_all_shelved : True.
Proof.
  assert (Hdispatch : ZesuStepSwitchDispatch) by constructor.
  zesu_dispatch_search constr:(@nil Prop) ltac:(fun _ => shelve).
  Unshelve.
  fixture_no_marker.
  exact I.
Qed.
Print Assumptions count_all_shelved.

Lemma count_existing_new_shared : (0 = 0) /\ (exists n : nat, n = n) /\ (3 = 3).
Proof.
  assert (Hdispatch : ZesuStepSwitchDispatch) by constructor.
  split; [shelve | split].
  1: zesu_dispatch_search constr:(@nil Prop) ltac:(fun _ => unshelve eexists; tryif lazymatch goal with |- nat => idtac end then shelve else idtac).
  1: ltac2:(fixture_exact_shared ()).
  2: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(3 = 3))).
  all: fixture_no_marker; reflexivity.
  Unshelve.
  1: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(0 = 0))).
  2: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(nat))).
  all: fixture_no_marker.
  1: reflexivity.
  1: exact O.
Qed.
Print Assumptions count_existing_new_shared.

Lemma count_mixed_groups : (0 = 0) /\ (1 = 1) /\ (2 = 2) /\ (3 = 3) /\ (4 = 4).
Proof.
  assert (Hdispatch : ZesuStepSwitchDispatch) by constructor.
  split; [shelve | idtac].
  zesu_dispatch_search constr:(@nil Prop) ltac:(fun _ => split; [shelve | split; [idtac | split; [shelve | idtac]]]).
  1: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(2 = 2))).
  2: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(4 = 4))).
  all: fixture_no_marker; reflexivity.
  Unshelve.
  1: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(0 = 0))).
  2: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(1 = 1))).
  3: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(3 = 3))).
  all: fixture_no_marker; reflexivity.
Qed.
Print Assumptions count_mixed_groups.

Lemma count_nested_shared : exists n : nat, n = n.
Proof.
  assert (Hdispatch : ZesuStepSwitchDispatch) by constructor.
  zesu_dispatch_search constr:(@nil Prop) ltac:(fun _ =>
    zesu_dispatch_search constr:(@nil Prop) ltac:(fun _ => unshelve eexists;
      tryif lazymatch goal with |- nat => idtac end then shelve else idtac)).
  ltac2:(fixture_exact_shared ()).
  fixture_no_marker; reflexivity.
  Unshelve.
  ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(nat))).
  fixture_no_marker; exact O.
Qed.
Print Assumptions count_nested_shared.

Lemma count_rollback_shared : exists n : nat, n = n.
Proof.
  assert (Hdispatch : ZesuStepSwitchDispatch) by constructor.
  zesu_dispatch_search constr:(@nil Prop) ltac:(fun _ =>
    first [unshelve eexists; fail 0 | unshelve eexists]).
  1: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(nat))).
  2: ltac2:(fixture_exact_shared ()).
  all: fixture_no_marker.
  1: exact O.
  all: reflexivity.
Qed.
Print Assumptions count_rollback_shared.

Lemma count_existing_new_shared_off : (0 = 0) /\ (exists n : nat, n = n) /\ (3 = 3).
Proof.
  split; [shelve | split].
  1: zesu_dispatch_search constr:(@nil Prop) ltac:(fun _ => unshelve eexists; tryif lazymatch goal with |- nat => idtac end then shelve else idtac).
  1: ltac2:(fixture_exact_shared ()).
  2: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(3 = 3))).
  all: fixture_no_marker; reflexivity.
  Unshelve.
  1: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(0 = 0))).
  2: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(nat))).
  all: fixture_no_marker.
  1: reflexivity.
  1: exact O.
Qed.
Print Assumptions count_existing_new_shared_off.

Lemma count_mixed_groups_off : (0 = 0) /\ (1 = 1) /\ (2 = 2) /\ (3 = 3) /\ (4 = 4).
Proof.
  split; [shelve | idtac].
  zesu_dispatch_search constr:(@nil Prop) ltac:(fun _ => split; [shelve | split; [idtac | split; [shelve | idtac]]]).
  1: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(2 = 2))).
  2: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(4 = 4))).
  all: fixture_no_marker; reflexivity.
  Unshelve.
  1: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(0 = 0))).
  2: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(1 = 1))).
  3: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(3 = 3))).
  all: fixture_no_marker; reflexivity.
Qed.
Print Assumptions count_mixed_groups_off.

Lemma wrapper_until_shared_off : (0 = 0) /\ (exists n : nat, n = n) /\ (3 = 3).
Proof.
  split; [shelve | split].
  1: zesu_run_until ltac:(fun _ => unshelve eexists;
    tryif lazymatch goal with |- nat => idtac end then shelve else idtac).
  1: ltac2:(fixture_exact_shared ()).
  2: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(3 = 3))).
  all: fixture_no_marker; reflexivity.
  Unshelve.
  1: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(0 = 0))).
  2: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(nat))).
  all: fixture_no_marker.
  1: reflexivity.
  1: exact O.
Qed.
Print Assumptions wrapper_until_shared_off.

Lemma wrapper_until_shared_on : (0 = 0) /\ (exists n : nat, n = n) /\ (3 = 3).
Proof.
  assert (Hdispatch : ZesuStepSwitchDispatch) by constructor.
  split; [shelve | split].
  1: zesu_run_until ltac:(fun _ => unshelve eexists;
    tryif lazymatch goal with |- nat => idtac end then shelve else idtac).
  1: ltac2:(fixture_exact_shared ()).
  2: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(3 = 3))).
  all: fixture_no_marker; reflexivity.
  Unshelve.
  1: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(0 = 0))).
  2: ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(nat))).
  all: fixture_no_marker.
  1: reflexivity.
  1: exact O.
Qed.
Print Assumptions wrapper_until_shared_on.

Lemma wrapper_run_shared_off (P : nat -> Prop) (H : forall n, P n) : exists n, P n.
Proof.
  eexists.
  zesu_run.
  all: fail "An active goal remains".
  Unshelve.
  ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(nat))).
  fixture_no_marker.
  exact O.
Qed.
Print Assumptions wrapper_run_shared_off.

Lemma wrapper_run_shared_on (P : nat -> Prop) (H : forall n, P n) : exists n, P n.
Proof.
  eexists.
  assert (Hdispatch : ZesuStepSwitchDispatch) by constructor.
  zesu_run.
  all: fail "An active goal remains".
  Unshelve.
  ltac2:(Control.assert_true (Constr.equal (Control.goal ()) constr:(nat))).
  fixture_no_marker.
  exact O.
Qed.
Print Assumptions wrapper_run_shared_on.

Lemma cache_present_certificate : True.
Proof.
  zesu_scope_switch_table (@nil (Prop * bool)) ltac:(fun _ => idtac).
  fixture_no_marker.
  exact I.
Qed.
Print Assumptions cache_present_certificate.

Lemma cache_absent_certificate : True.
Proof.
  zesu_scope_switch_table (@nil (Prop * bool)) ltac:(fun _ =>
    lazymatch goal with H : ZesuSwitchDispatchCache _ |- _ => clear H end).
  fixture_no_marker.
  exact I.
Qed.
Print Assumptions cache_absent_certificate.

Lemma cache_closed_certificate : True.
Proof.
  zesu_scope_switch_table (@nil (Prop * bool)) ltac:(fun _ => exact I).
Qed.
Print Assumptions cache_closed_certificate.

Lemma cache_dependent_clear_failure : True.
Proof.
  assert_fails (zesu_scope_switch_table (@nil (Prop * bool)) ltac:(fun _ =>
    lazymatch goal with H : ZesuSwitchDispatchCache _ |- _ =>
      pose proof (eq_refl H) as dependent end)).
  fixture_no_marker.
  exact I.
Qed.
Print Assumptions cache_dependent_clear_failure.

Lemma cache_action_failure_rollback : True.
Proof.
  assert_fails (zesu_scope_switch_table (@nil (Prop * bool)) ltac:(fun _ =>
    evar (inside : nat); fail 0 "The fixture action failed")).
  fixture_no_marker.
  exact I.
Qed.
Print Assumptions cache_action_failure_rollback.

Lemma cache_absent_with_existing_shelf : True /\ True.
Proof.
  split; [shelve | idtac].
  zesu_scope_switch_table (@nil (Prop * bool)) ltac:(fun _ =>
    lazymatch goal with H : ZesuSwitchDispatchCache _ |- _ => clear H end).
  fixture_no_marker; exact I.
  Unshelve.
  fixture_no_marker; exact I.
Qed.
Print Assumptions cache_absent_with_existing_shelf.

Lemma cache_nested_present : True.
Proof.
  zesu_scope_switch_table (@nil (Prop * bool)) ltac:(fun _ =>
    zesu_scope_switch_table (@nil (Prop * bool)) ltac:(fun _ => idtac);
    lazymatch goal with _ : ZesuSwitchDispatchCache _ |- _ => idtac end).
  fixture_no_marker.
  exact I.
Qed.
Print Assumptions cache_nested_present.

Lemma cache_nested_absent : True.
Proof.
  zesu_scope_switch_table (@nil (Prop * bool)) ltac:(fun _ =>
    zesu_scope_switch_table (@nil (Prop * bool)) ltac:(fun _ =>
      lazymatch goal with H : ZesuSwitchDispatchCache _ |- _ => clear H end);
    lazymatch goal with _ : ZesuSwitchDispatchCache _ |- _ => idtac end).
  fixture_no_marker.
  exact I.
Qed.
Print Assumptions cache_nested_absent.
