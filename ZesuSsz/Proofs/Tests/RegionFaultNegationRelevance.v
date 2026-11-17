From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The goal's pruned context keeps a negation that shares a variable with the
   goal, directly or through other facts, and drops an unrelated one. *)
Lemma region_goal_keeps_related (x y w z : Z)
    (Hdirect : ~ x = 3) (Hlink : w = y) (Hthrough : ~ w = 4) (Hother : ~ z = 5) :
  x <= y \/ x > y.
Proof.
  assert_succeeds (ZesuSsz.Automation2.UnionRuleComponents.zesu_region_goal_keeps Hdirect).
  assert_succeeds (ZesuSsz.Automation2.UnionRuleComponents.zesu_region_goal_keeps Hthrough).
  Fail ZesuSsz.Automation2.UnionRuleComponents.zesu_region_goal_keeps Hother.
  lia.
Qed.

(* A contradiction away from the goal still closes the bound. *)
Lemma region_fault_unrelated_contradiction (x y z : Z) (Hz : z = 3) (Hne : ~ z = 3) :
  x <= y.
Proof. ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_bound_if_enabled. Qed.

(* A related negation that the facts do not refute is not retried; the bound
   fails. *)
Lemma region_fault_related_negation_refused (x y : Z) (Hne : ~ x = 3) : True.
Proof.
  Fail (assert (x <= y) by
    ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_bound_if_enabled).
  exact I.
Qed.
