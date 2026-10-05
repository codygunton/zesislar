Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.InstructionLookup.
Require Import ZesuSsz.Automation.Switches.RamFault.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemJoinTransfers.
From iris.proofmode Require Import environments.
Open Scope Z_scope.
Require Import ZesuSsz.Contracts.DecodeItemErrorBranch.

Lemma decodeItemErrorMaskBridge_correct `{!islaG Sigma} `{!threadG}
    args (frameBytes : list byte) (lengthRegister : bv 64) :
  ⊢ decodeItemJoinTransferObligation 0x800d69e0 0x800d69e4
    (⌜Z.land (bv_unsigned lengthRegister) 127 >=
       decodeItemInputLength args⌝ ∗
     decodeItemEntryAt800d69e0 args frameBytes lengthRegister)%I
    (decodeItemErrorBranchEntry args frameBytes
      (bv_and lengthRegister 127)).
Proof.
  unfold decodeItemJoinTransferObligation, decodeItemErrorBranchEntry.
  iIntros "Hcode".
  iEval (unfold decodeItemSelectedCode) in "Hcode".
  iDestruct "Hcode" as "#Hcode".
  zesu_block.
  apply decodeItemErrorMaskedLengthGuard; assumption.
Qed.

Print Assumptions decodeItemErrorMaskBridge_correct.
