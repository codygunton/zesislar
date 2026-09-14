Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.CallScratchSized.
Require Import isla.riscv64.riscv64.

Lemma scratch_reuse_sized_keeps_frame `{!islaG Sigma}
    (sp ret : bv 64) (bytes : list (bv 8)) (size : N) (P : iProp Sigma) :
  length bytes = N.to_nat size ->
  ((mapRamBase defaultMap) <= bv_unsigned sp - (Z.of_N size + 16))%Z ->
  (bv_unsigned (sp - Z_to_bv 64 (Z.of_N size + 16))%bv ↦ₘ∗ bytes ∗
   (bv_unsigned sp - 16) ↦ₘ? 8 ∗ (bv_unsigned sp - 8) ↦ₘ ret ∗ P ∗ True)%I -∗
  ((bv_unsigned sp - (Z.of_N size + 16)) ↦ₘ? (Z.of_N size + 16) ∗ P ∗ True)%I.
Proof.
  intros Hlen Hlow. iIntros "(Hbytes & Hgap & Hret & HP & _)".
  iPoseProof (call_scratch_reuse_sized sp ret bytes size Hlen Hlow
    with "[$Hbytes $Hgap $Hret]") as "Hscratch".
  iFrame.
Qed.
Print Assumptions scratch_reuse_sized_keeps_frame.
