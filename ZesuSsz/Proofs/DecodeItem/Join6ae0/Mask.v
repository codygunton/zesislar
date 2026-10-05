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
    args (frameBytes : list byte) (lengthRegister : bv 64)
    (inputPrefix : byte) (rest : list byte) :
  ⊢ decodeItemJoinTransferObligation 0x800d69e0 0x800d69e4
    (⌜Z.land (bv_unsigned lengthRegister) 127 >=
       decodeItemInputLength args⌝ ∗
     decodeItemEntryAt800d69e0 args frameBytes lengthRegister inputPrefix rest)%I
    (decodeItemErrorBranchEntry args frameBytes
      (bv_and lengthRegister 127) inputPrefix rest).
Proof.
  unfold decodeItemJoinTransferObligation, decodeItemErrorBranchEntry.
  iIntros "Hcode".
  iEval (unfold decodeItemSelectedCode) in "Hcode".
  iDestruct "Hcode" as "#Hcode".
  zesu_block.
  all: try (apply decodeItemErrorMaskedLengthGuard; assumption).
  all: rewrite bv_and_unsigned.
  all: match goal with Hprefix : bv_unsigned ?x = bv_unsigned ?y |- _ => rewrite Hprefix end.
  all: change (Z.land (bv_unsigned inputPrefix) (Z.ones 7) = bv_unsigned inputPrefix - 128).
  all: rewrite (Z.land_ones _ 7 ltac:(lia)); cbn; symmetry; apply Z.mod_unique with (q := 1); lia.
Qed.

Print Assumptions decodeItemErrorMaskBridge_correct.
