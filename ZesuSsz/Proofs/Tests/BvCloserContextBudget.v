From Coq Require Import ZArith.ZArith Lists.List.
From Ltac2 Require Import Ltac2.
Import ListNotations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.LinearFirstLia.
Require Import ZesuSsz.Automation2.All.
Set Default Proof Mode "Classic".
Local Open Scope Z_scope.

#[local] Instance bv_closer_budget_finisher_once :
  ZesuSsz.Automation2.ContextCollection.ZesuStepFinisherOnce := I.

(* The lower bound counts a collapsed application as one node:
   `bv_unsigned a < bv_unsigned b + 5` is 2 + 1 + (2 + 1 + 7) = 13 nodes. *)
Goal forall a b : bv 64, bv_unsigned a < bv_unsigned b + 5 -> True.
Proof.
  intros a b H.
  ltac2:(zesu_linear_collapsed_facts_within [constr:(@bv_unsigned)] 14).
  Fail ltac2:(zesu_linear_collapsed_facts_within [constr:(@bv_unsigned)] 13).
  Fail ltac2:(zesu_linear_collapsed_facts_within [] 14).
  exact I.
Qed.

(* A fact of about 120000 nodes on an unrelated variable puts the context above
   the whole-context budget: the closer's whole-context run is refused before
   it saturates, and the pruned run still closes the goal. *)
Lemma bv_closer_whole_context_refused (a : bv 64) (y : Z) :
  bv_unsigned a < 10 -> bv_unsigned a < 11.
Proof.
  intro Ha.
  let n := eval vm_compute in (Z.to_nat 20000) in
  let big := eval cbv [fold_right repeat] in (fold_right Z.add 0 (repeat y n)) in
  pose proof (eq_refl : big = big) as Hbig.
  Fail ZesuSsz.Automation2.Hooks.zesu_bv_closer_context_within_budget.
  ZesuSsz.Automation2.Hooks.zesu_bv_context_filter
    ltac:(ZesuSsz.Automation2.Hooks.zesu_bv_solve_closer).
Qed.

(* Without the large fact the whole-context run is allowed. *)
Lemma bv_closer_whole_context_allowed (a : bv 64) :
  bv_unsigned a < 10 -> bv_unsigned a < 11.
Proof.
  intro Ha.
  ZesuSsz.Automation2.Hooks.zesu_bv_closer_context_within_budget.
  bv_solve.
Qed.
