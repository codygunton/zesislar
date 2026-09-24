Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Switches.FourWordScratch.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.

Lemma test_four_word_scratch `{!islaG Sigma} (sp : bv 64) :
  writeSuccessStorageKeysScratch sp -∗
  (∃ x : bv 64 *ₗ bv 64 *ₗ bv 64 *ₗ bv 64 *ₗ (),
    (bv_unsigned sp + 1712) ↦ₘ x.4ₗ ∗
    (bv_unsigned sp + 1720) ↦ₘ x.3ₗ ∗
    (bv_unsigned sp + 1728) ↦ₘ x.2ₗ ∗
    (bv_unsigned sp + 1736) ↦ₘ x.1ₗ ∗ True)%I.
Proof.
  iIntros "Hscratch".
  zesu_rule_set_v2_steps.
Qed.
Print Assumptions test_four_word_scratch.
