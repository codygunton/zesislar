Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CanonicalFactAdapter.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.
Local Open Scope Z_scope.

#[local] Instance canonical_fact_once_enabled :
  ZesuSsz.Automation.CanonicalFactAdapter.ZesuStepCanonicalFactAdapter := I.

Lemma canonical_fact_views_fire_once (x y : Z) (Hxy : x <= y) :
  bool_decide (x <= y) = true.
Proof.
  Hooks.zesu_canonical_fact_views_if_enabled.
  assert_fails Hooks.zesu_canonical_fact_views_if_enabled.
  assumption.
Qed.

Lemma canonical_fact_views_follow_new_goal (x y : Z) (Hxy : x <= y) :
  bool_decide (x <= y) = true.
Proof.
  pose proof (@Hooks.zesu_canonical_fact_views_token Prop True) as Hprevious.
  Hooks.zesu_canonical_fact_views_if_enabled.
  assumption.
Qed.

Section StuckMemory.
  Context (Sigma : gFunctors) (islaG0 : islaG Sigma) (Hthread : threadG).
  Local Existing Instance islaG0.
  Local Existing Instance Hthread.
  Context (pointer : bv 64) (x y : Z) (Hxy : x <= y).

  Goal (⊢ find_in_context (FindMemMapsTo (bv_unsigned pointer))
    (fun _ => False%I))%I.
  Proof.
    iStartProof.
    Hooks.zesu_canonical_fact_views_if_enabled.
    match goal with _ : bool_decide (x <= y) = true |- _ => idtac end.
    assert_fails Hooks.zesu_canonical_fact_views_if_enabled.
    repeat Hooks.zesu_canonical_fact_views_if_enabled.
  Abort.
End StuckMemory.
