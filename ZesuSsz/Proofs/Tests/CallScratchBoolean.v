Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CallScratchBoolean.
Require Import isla.riscv64.riscv64.

Lemma call_boolean_scratch_preserves_frame `{!islaG Sigma}
    (sp ret : bv 64) (byte : bv 8) (P : iProp Sigma) :
  ((bv_unsigned sp - 16) ↦ₘ? 7 ∗ (bv_unsigned sp - 9) ↦ₘ byte ∗
   (bv_unsigned sp - 8) ↦ₘ ret ∗ P ∗ True)%I -∗
  (bv_unsigned sp - 16) ↦ₘ? 16 ∗ P ∗ True.
Proof.
  iIntros "(Hgap & Hbyte & Hret & HP & _)".
  iFrame "HP". iApply (call_boolean_scratch_reuse with "[$Hgap $Hbyte $Hret]").
Qed.
Print Assumptions call_boolean_scratch_preserves_frame.
