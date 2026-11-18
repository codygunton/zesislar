From Coq Require Import ZArith.ZArith Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

#[local] Instance region_negation_finisher_once :
  ZesuSsz.Automation2.ContextCollection.ZesuStepFinisherOnce := I.

(* A fact of about 120000 nodes on w puts the context above the whole-context
   budget, so the goal run sees only the facts that share x or y and fails. The
   contradiction through z is found only by retrying a negation. *)

(* A negated inequality is retried and refutes the context. *)
Lemma region_fault_negated_inequality_retried (w x y z : Z)
    (Hz : 5 <= z) (Hne : ~ (z >= 3)) :
  x <= y.
Proof.
  let n := eval vm_compute in (Z.to_nat 20000) in
  let big := eval cbv [fold_right repeat] in (fold_right Z.add 0 (repeat w n)) in
  pose proof (eq_refl : big = big) as Hbig.
  Fail bv_solve.
  ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_arithmetic_full.
Qed.

(* A negated equality is a branch disequality and is not retried with bv_solve;
   the library lia fallback sees the whole context, refutes it, and closes the
   goal. *)
Lemma region_fault_negated_equality_library_fallback (w x y z : Z)
    (Hz : z = 3) (Hne : ~ z = 3) :
  x <= y.
Proof.
  let n := eval vm_compute in (Z.to_nat 20000) in
  let big := eval cbv [fold_right repeat] in (fold_right Z.add 0 (repeat w n)) in
  pose proof (eq_refl : big = big) as Hbig.
  Fail bv_solve.
  ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_arithmetic_full.
Qed.
