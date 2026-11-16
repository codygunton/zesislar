From Coq Require Import ZArith.ZArith Lists.List.
Import ListNotations.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* Every solver engine runs through BoundedSolve: the pruned arm and the
   whole-context arm each refuse a context above their node budget, a
   saturation is skipped on such a context, a view closer fails on it, and a
   VM run refuses a large goal. The prune keeps a fact only within its linking
   rounds. *)
#[local] Instance bounded_solve_finisher_once :
  ZesuSsz.Automation2.ContextCollection.ZesuStepFinisherOnce := I.

Ltac bounded_solve_big_fact x count :=
  let n := eval vm_compute in (Z.to_nat count) in
  let big := eval cbv [fold_right repeat] in (fold_right Z.add 0 (repeat x n)) in
  pose proof (eq_refl : big = big).

Lemma bounded_bv_refuses_large_context (x : bv 64) :
  bv_unsigned x <= 5 -> bv_unsigned x <= 6.
Proof.
  intro Hx.
  bounded_solve_big_fact (bv_unsigned x) 20000.
  match goal with H : _ = _ |- _ => rename H into Hbig end.
  Fail ZesuSsz.Automation2.BoundedSolve.zesu_bounded_bv_with ltac:(fail).
  clear Hbig.
  ZesuSsz.Automation2.BoundedSolve.zesu_bounded_bv_with ltac:(fail).
Qed.

Lemma bounded_saturation_skips_large_context (x : Z) : True.
Proof.
  Fail ZesuSsz.Automation2.BoundedSolve.zesu_bounded_saturate ltac:(fail).
  ZesuSsz.Automation2.BoundedSolve.zesu_bounded_views ltac:(idtac).
  bounded_solve_big_fact x 100000.
  ZesuSsz.Automation2.BoundedSolve.zesu_bounded_saturate ltac:(fail).
  Fail ZesuSsz.Automation2.BoundedSolve.zesu_bounded_views ltac:(idtac).
  exact I.
Qed.

Lemma bounded_vm_refuses_large_goal (x : Z) : True.
Proof.
  assert (Hsmall : 1 + 1 = 2) by (ZesuSsz.Automation2.BoundedSolve.zesu_vm_compute_goal; reflexivity).
  let n := eval vm_compute in (Z.to_nat 10000) in
  let big := eval cbv [fold_right repeat] in (fold_right Z.add 0 (repeat 1 n)) in
  assert (Hlarge : big = 10000) by
    (tryif ZesuSsz.Automation2.BoundedSolve.zesu_vm_compute_goal then fail else idtac;
     vm_compute; reflexivity).
  exact I.
Qed.

(* Facts are numbered by the round that links them: within six rounds the
   sixth stays, the seventh is unrelated. *)
Lemma bounded_prune_keeps_six_rounds (x0 x1 x2 x3 x4 x5 x6 x7 : Z)
    (H1 : x0 = x1) (H2 : x1 = x2) (H3 : x2 = x3) (H4 : x3 = x4) (H5 : x4 = x5)
    (H6 : x5 = x6) (H7 : x6 = x7) :
  x0 = x0.
Proof.
  ZesuSsz.Automation2.BoundedSolve.zesu_bounded_prune_goal.
  let kept := type of H6 in idtac.
  Fail let dropped := type of H7 in idtac.
  reflexivity.
Qed.

(* A proof search runs on the pruned context within the search budget: it
   closes a goal from a related fact, and a related context above the budget
   refuses it. *)
Lemma bounded_search_within_the_pruned_budget (P : Z -> Prop) (x : Z)
    (Hp : P x) : P x \/ False.
Proof.
  assert (Hpx : P x) by ZesuSsz.Automation2.BoundedSolve.zesu_bounded_search ltac:(eauto).
  bounded_solve_big_fact x 100000.
  tryif ZesuSsz.Automation2.BoundedSolve.zesu_bounded_search ltac:(eauto) then fail else idtac.
  left; exact Hpx.
Qed.
