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
