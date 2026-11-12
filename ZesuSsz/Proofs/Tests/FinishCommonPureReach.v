From Coq Require Import ZArith.ZArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The common pure path runs when the first arm of the final finisher
   leaves the goal open. The bound sits inside a folded domain predicate, as in the
   side conditions of `subsume_uninit_region_crossing`: `lia` reads the
   predicate as an atom, and only the common path opens it. *)
Record reach_args := { reach_cursor : Z; reach_length : Z }.

Definition reach_domain (args : reach_args) : Prop :=
  0 <= reach_cursor args /\ 0 <= reach_length args /\
  reach_cursor args + reach_length args < 2 ^ 64.

Lemma finish_final_pure_opens_folded_domain (args : reach_args) :
  reach_domain args -> reach_cursor args - 8 + 8 < 2 ^ 64.
Proof. intros Hdomain. zesu_finish_final_pure. Qed.

(* A bound the facts do not give stays open, and each finisher still
   succeeds on it, as before. *)
Lemma finishers_keep_open_bound (args : reach_args) : reach_domain args -> True.
Proof.
  intros Hdomain.
  assert_fails (assert (reach_cursor args < 5) by zesu_finish).
  assert_succeeds (assert (reach_cursor args < 5); [zesu_finish |]).
  assert_succeeds (assert (reach_cursor args < 5); [zesu_finish_final_pure |]).
  assert_succeeds (assert (reach_cursor args < 5); [zesu_finish_pure_goal |]).
  exact I.
Qed.

(* The fallthrough runs only on goals without open evars. *)
Lemma goal_without_evars_guard (args : reach_args) : reach_domain args -> True.
Proof.
  intros Hdomain.
  assert_succeeds (assert (reach_cursor args - 8 + 8 < 2 ^ 64);
    [ZesuSsz.Automation2.Finish.zesu_goal_without_evars; zesu_finish_final_pure |]).
  assert_fails (eassert (reach_cursor args - 8 + 8 < ?[bound]);
    [ZesuSsz.Automation2.Finish.zesu_goal_without_evars |]).
  assert_fails (eassert (?[witness] = reach_cursor args -> True);
    [intros Hwitness; ZesuSsz.Automation2.Finish.zesu_goal_without_evars |]).
  exact I.
Qed.
