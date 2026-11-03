Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.RewriteBoundGuards.
From Coq Require Import ZArith.ZArith.
From stdpp Require Import bitvector.definitions bitvector.tactics.
Require Import ZesuSsz.Automation.All.
Local Open Scope Z_scope.

Lemma rewrite_bound_switch_off385 : True.
Proof.
  assert (Hcache : ZesuSsz.Automation.SwitchDispatch.ZesuSwitchDispatchCache
    (cons (ZesuStepRewriteBoundGuards, false) nil)) by constructor.
  assert_fails (assert (0 <= 7) by a3n_closed_bound_if_enabled).
  exact I.
Qed.

Section Enabled.
  #[local] Instance rewrite_bound_on385 : ZesuStepRewriteBoundGuards := I.

  Lemma rewrite_bound_closed385 : 0 <= 7 < 2 ^ 64.
  Proof. a3n_closed_bound_if_enabled. Qed.

  Lemma rewrite_bound_false_refusal385 : True.
  Proof.
    assert_fails (assert (8 <= 7) by a3n_closed_bound_if_enabled).
    exact I.
  Qed.

  Lemma rewrite_bound_symbolic_refusal385 (x : Z) : x <= x + 1.
  Proof.
    assert_fails (idtac; a3n_closed_bound_if_enabled).
    Lia.lia.
  Qed.

  Lemma rewrite_bound_original_fallback385 (x : Z) : x <= x + 1.
  Proof. bv_solve. Qed.

  Lemma rewrite_bound_consumer385 (base : bv 64)
      (Hbound : bv_unsigned base + 7 < 2 ^ 64) :
    bv_unsigned (base + Z_to_bv 64 7)%bv - bv_unsigned base = 7.
  Proof.
    rewrite zesu_bv_unsigned_add_Z_64;
      try reflexivity; bv_solve.
  Qed.
End Enabled.
