Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.UninitWords.
Require Import isla.riscv64.riscv64.

Lemma test_four_scratch_words `{!islaG Sigma} (sp : Z) :
  (mapRamBase defaultMap) <= sp -> sp + 1896 < (machineRamEnd defaultMap) ->
  (sp + 1712) ↦ₘ? 32 -∗
  ∃ first second third fourth : bv 64,
    (sp + 1712) ↦ₘ first ∗ (sp + 1720) ↦ₘ second ∗
    (sp + 1728) ↦ₘ third ∗ (sp + 1736) ↦ₘ fourth ∗ True.
Proof.
  intros Hlow Hhigh. iStartProof. iIntros "Hscratch". zesu_run.
Qed.
Print Assumptions test_four_scratch_words.
