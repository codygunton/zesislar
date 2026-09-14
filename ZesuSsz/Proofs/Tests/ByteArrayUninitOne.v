Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsTypeSourceEntry.
Require Import ZesuSsz.Automation.ByteScratch.

Lemma test_byte_array_one_uninit_subsumption `{!islaG Sigma}
    (sp : bv 64) (byte : bv 8) :
  0x20000000 <= bv_unsigned sp ->
  bv_unsigned sp + 1896 < 0x40000000 ->
  (bv_unsigned sp + 1745) ↦ₘ? 19 -∗
  subsume (bv_unsigned (sp + BV 64 1744)%bv ↦ₘ∗ [byte])
    (fun _ : unit => (bv_unsigned sp + 1744) ↦ₘ? 20) (fun _ => True%I).
Proof.
  intros Hlow Hhigh. iStartProof. iIntros "Htail".
  zesu_run.
Qed.
Print Assumptions test_byte_array_one_uninit_subsumption.
