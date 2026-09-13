Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Import ZesuSsz.Automation.Calls.FramedContinuations.

Lemma optional_scratch_cleanup `{!islaG Sigma} `{!threadG}
    (sp ret : bv 64) (payload : bv 8) (P : iProp Sigma) :
  (bv_unsigned sp - 32) ↦ₘ? 7 ∗
  (bv_unsigned sp - 25) ↦ₘ∗ [payload] ∗
  (bv_unsigned sp - 24) ↦ₘ ret ∗
  (bv_unsigned sp - 16) ↦ₘ? 16 ∗ P ∗ True -∗
  (bv_unsigned sp - 32) ↦ₘ? 32 ∗ P ∗ True.
Proof. iStartProof. zesu_run. Qed.

Print Assumptions optional_scratch_cleanup.

Lemma optional_scratch_continuation `{!islaG Sigma} `{!threadG}
    (sp ret : bv 64) (payload : bv 8) (P : iProp Sigma) :
  instr_pre (bv_unsigned ret) ((bv_unsigned sp - 32) ↦ₘ? 32 ∗ P ∗ True) -∗
  instr_pre (bv_unsigned ret)
    ((bv_unsigned sp - 32) ↦ₘ? 7 ∗
     (bv_unsigned sp - 25) ↦ₘ∗ [payload] ∗
     (bv_unsigned sp - 24) ↦ₘ ret ∗
     (bv_unsigned sp - 16) ↦ₘ? 16 ∗ P ∗ True).
Proof. iStartProof. zesu_run. Qed.

Print Assumptions optional_scratch_continuation.

Lemma optional_scratch_wand_and_continuation `{!islaG Sigma} `{!threadG}
    (sp ret : bv 64) (payload : bv 8) (P Q : iProp Sigma) :
  instr_body (bv_unsigned ret) Q -∗
  (((bv_unsigned sp - 32) ↦ₘ? 7 ∗
     (bv_unsigned sp - 25) ↦ₘ∗ [payload] ∗
     (bv_unsigned sp - 24) ↦ₘ ret ∗
     (bv_unsigned sp - 16) ↦ₘ? 16 ∗ P ∗ True -∗
     (bv_unsigned sp - 32) ↦ₘ? 32 ∗ P ∗ True) ∗
   True ∗ instr_pre (bv_unsigned ret) Q ∗ True).
Proof. iStartProof. iIntros "Hnext". zesu_run. Qed.

Print Assumptions optional_scratch_wand_and_continuation.

Definition optionalScratchAlias `{!islaG Sigma} (P : iProp Sigma) : iProp Sigma := P.
Global Instance : LithiumUnfold (@optionalScratchAlias) := I.

Lemma optional_scratch_identity_wand `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  ⊢ ((P ∗ True -∗ optionalScratchAlias P ∗ True) ∗ True ∗ True ∗ True)%I.
Proof. iStartProof. zesu_run. Qed.

Print Assumptions optional_scratch_identity_wand.

Lemma optional_scratch_address (sp : bv 64) :
  (sp - BV 64 16 - BV 64 9)%bv = (sp - BV 64 25)%bv.
Proof. autorewrite with zesu_indices. reflexivity. Qed.

Print Assumptions optional_scratch_address.
