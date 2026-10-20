Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Compliance.DecodeItemSavedFrameWitnesses.
Require Import ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.
Require Import ZesuSsz.Compliance.DecodeItemMaskedReturnFacts.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.

Set Printing Width 200.
Require Import isla.isla.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Stock.Closure.index_decodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Automation.ReturnWand.
Require Import ZesuSsz.Automation.ReturnWand.
(* Native successor capture; no resources added. *)
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Automation.ReturnWand.

Definition DesignedEntry_800d6960
    `{!islaG Sigma} `{!threadG} (returnAddress : Z) (args : DecodeItemArgs) : iProp Sigma :=
  ((ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6960 (returnAddress) (args)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6960) := I.
Global Typeclasses Opaque DesignedEntry_800d6960.


Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Lemma DesignedBoundary_800d6960 `{!islaG Sigma} `{!threadG} (returnAddress : Z) (args : DecodeItemArgs)   :
  instr_pre 0x800d6974 (∃ (successor_frameBytes : list byte) (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6974 (args) (successor_frameBytes) (successor_inputPrefix) (successor_rest))%I -∗
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6960
    (DesignedEntry_800d6960 returnAddress args).
Proof.
 zesu_block.
Qed.
