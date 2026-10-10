Require Import ZesuSsz.Automation.All.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Compliance.DecodeItemStringSuccessorWitnesses.
Open Scope Z_scope.

Lemma decodeItemStringFlagUnitOn `{!islaG Sigma} `{!threadG}
    (b : bv 64) (remaining : isla_trace) :
  Z.land (bv_unsigned b) 131072 = 0 ->
  wp_asm remaining -∗
  (∃ _ : unit, LET_ID (fun v : base_val => ⌜v = Val_Bool true⌝ ∗ wp_asm remaining)
    (Val_Bool (bool_decide (bv_and b 131072 = 0%bv))))%I.
Proof.
  intros Hflag. iIntros "Hremaining".
  zesu_pure_fact_hints_if_enabled.
  iFrame.
Qed.

Lemma decodeItemStringFlagUnitExistentialOn `{!islaG Sigma} `{!threadG}
    (b : bv 64) (remaining : isla_trace) :
  Z.land (bv_unsigned b) 131072 = 0 ->
  wp_asm remaining -∗
  (∃ _ : unit, ⌜Val_Bool (bool_decide (bv_and b 131072 = 0%bv)) = Val_Bool true⌝ ∗ wp_asm remaining)%I.
Proof.
  intros Hflag. iIntros "Hremaining".
  zesu_pure_fact_existential_if_enabled.
  iFrame.
Qed.

Lemma decodeItemStringFlagUnitLocalAliasOn `{!islaG Sigma} `{!threadG}
    (b : bv 64) (remaining : isla_trace) :
  Z.land (bv_unsigned b) 131072 = 0 ->
  wp_asm remaining -∗
  (∃ _ : unit, LET_ID (fun v : base_val => ⌜v = Val_Bool true⌝ ∗ wp_asm remaining)
    (Val_Bool (bool_decide (bv_and b 131072 = 0%bv))))%I.
Proof.
  intros Hflag.
  pose (LET_GOAL := LET_ID (fun v : base_val => (⌜v = Val_Bool true⌝ ∗ wp_asm remaining)%I)).
  change (⊢ wp_asm remaining -∗
    (∃ _ : unit, LET_GOAL (Val_Bool (bool_decide (bv_and b 131072 = 0%bv)))))%I.
  iIntros "Hremaining".
  zesu_pure_fact_hints_if_enabled.
  iFrame.
Qed.

Lemma decodeItemStringFlagUnitMissingGuardRejected `{!islaG Sigma} `{!threadG}
    (b : bv 64) (remaining : isla_trace) : True.
Proof.
  Fail let evidence := constr:(_ : ZesuPureFactIntro
    (∃ _ : unit, LET_ID (fun v : base_val => ⌜v = Val_Bool true⌝ ∗ wp_asm remaining)
      (Val_Bool (bool_decide (bv_and b 131072 = 0%bv))))%I _) in idtac evidence.
  exact I.
Qed.
Print Assumptions decodeItemStringFlagUnitOn.
Print Assumptions decodeItemStringFlagUnitExistentialOn.
Print Assumptions decodeItemStringFlagUnitLocalAliasOn.
Print Assumptions decodeItemStringFlagUnitMissingGuardRejected.
