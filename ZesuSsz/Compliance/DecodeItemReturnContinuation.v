Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.

Lemma decodeItemFixedOutcomeContinuation `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (outcome : DecodeItemOutcome) :
  decodeItemBranchContinuation args -∗
  instr_pre (decodeItemReturnAddress args)
    (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      DecodeMeaningModuloKnownBugs args outcome⌝ ∗
     decodeItemExitResources args outcome ∗ True).
Proof.
  unfold decodeItemBranchContinuation, decodeItemBranchContinuationAt.
  iIntros "Hcontinuation".
  iApply (instr_pre_wand with "Hcontinuation"); [done|done|].
  iIntros "[Hfacts [Hresources _]]".
  iExists outcome. iFrame.
Qed.

Print Assumptions decodeItemFixedOutcomeContinuation.
