Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CallScratchBytes.
Require Import isla.riscv64.riscv64.

Lemma test_call_bytes_scratch_frame `{!islaG Sigma}
    (sp ret countret stack2 old9 old8 : bv 64) (bytes source : list (bv 8))
    (address : Z) (P : iProp Sigma) :
  length bytes = 8%nat -> (0x20000000 <= bv_unsigned sp - 48)%Z ->
  (bv_unsigned (sp - BV 64 48)%bv ↦ₘ∗ bytes ∗
   (bv_unsigned sp - 40) ↦ₘ countret ∗ (bv_unsigned sp - 32) ↦ₘ stack2 ∗
   (bv_unsigned sp - 24) ↦ₘ old9 ∗ (bv_unsigned sp - 16) ↦ₘ old8 ∗
   (bv_unsigned sp - 8) ↦ₘ ret ∗ address ↦ₘ∗ source ∗ P ∗ True)%I -∗
  ((bv_unsigned sp - 48) ↦ₘ? 48 ∗ address ↦ₘ∗ source ∗ P ∗ True)%I.
Proof.
  intros Hlen Hlow. iIntros "(Hbytes & H0 & H1 & H2 & H3 & H4 & Hsource & HP & _)".
  iFrame "Hsource HP". iApply (call_bytes_scratch_reuse sp ret countret stack2 old9 old8 bytes Hlen Hlow
    with "[$Hbytes $H0 $H1 $H2 $H3 $H4]").
Qed.
Print Assumptions test_call_bytes_scratch_frame.
