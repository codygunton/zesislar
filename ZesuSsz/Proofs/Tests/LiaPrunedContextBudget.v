From Coq Require Import ZArith.ZArith Lists.List.
Import ListNotations.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The lia override's pruned arm keeps every fact that shares a variable with
   the goal. A fact of about 120000 nodes on the goal's variable stays in the
   pruned context, above the pruned-context budget, so the arm refuses it as
   the whole-context arm does; once the fact is gone, the same goal closes.
   The test calls the bounded arm directly: the override's earlier arms close
   this goal first. *)
#[local] Instance lia_pruned_budget_finisher_once :
  ZesuSsz.Automation2.ContextCollection.ZesuStepFinisherOnce := I.

Lemma lia_pruned_context_within_budget (x : Z) :
  x <= 5 -> x <= 6.
Proof.
  intro Hx.
  let n := eval vm_compute in (Z.to_nat 20000) in
  let big := eval cbv [fold_right repeat] in (fold_right Z.add 0 (repeat x n)) in
  pose proof (eq_refl : big = big) as Hbig.
  Fail ZesuSsz.Automation2.Hooks.zesu_lia_context_bounded
    ltac:(ZesuSsz.Automation2.LinearFirstLia.zesu_lia_linear_first3).
  clear Hbig.
  ZesuSsz.Automation2.Hooks.zesu_lia_context_bounded
    ltac:(ZesuSsz.Automation2.LinearFirstLia.zesu_lia_linear_first3).
Qed.
