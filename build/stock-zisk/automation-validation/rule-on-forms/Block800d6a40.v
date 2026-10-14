Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.
Require Import ZesuSsz.Compliance.DecodeItemLongStringOutputMeaning.
Require Import ZesuSsz.Contracts.DecodeItemFrameImage.
Require Import isla.isla.
Require Import ZesuSsz.Stock.Closure.index_decodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Automation.ReturnWand.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
From iris.proofmode Require Import environments.

Definition DesignedEntry_800d6a40
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte) (headerLength : Z) (payloadLength : Z) : iProp Sigma :=
  ((ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6a40 (args) (locals) (inputPrefix) (rest) (headerLength) (payloadLength)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6a40) := I.
Global Typeclasses Opaque DesignedEntry_800d6a40.

Lemma DesignedBoundary_800d6a40 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte) (headerLength : Z) (payloadLength : Z)  :
  decodeItemSelectedCode -∗
  instr_body 0x800d6a40
    (DesignedEntry_800d6a40 args locals inputPrefix rest headerLength payloadLength).
Proof.
zesu_block.
apply ZesuSsz.Compliance.DecodeItemExitMeanings.decodeItemReturn6a40Meaning.
Qed.
