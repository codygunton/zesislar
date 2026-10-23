Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Generated.DecodeItem.Entries.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Compliance.DecodeItemLoopInitialization.
Require Import isla.isla.
Require Import ZesuSsz.Stock.Closure.index_decodeItem.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Automation.ReturnWand.
From iris.proofmode Require Import environments.

Definition DesignedEntry_800d6a14
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (oldAcc : bv 64) (oldCursor : bv 64) (loaded : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a14 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (oldAcc) (oldCursor) (loaded) (inputPrefix) (rest)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6a14) := I.
Global Typeclasses Opaque DesignedEntry_800d6a14.

Lemma DesignedBoundary_800d6a14 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (oldAcc : bv 64) (oldCursor : bv 64) (loaded : bv 64) (inputPrefix : byte) (rest : list byte)  :
  instr_pre 0x800d6a24 (∃ (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a24 (args) (successor_inputPrefix) (successor_rest))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a14
    (DesignedEntry_800d6a14 args n payloadStart lengthBytes frameBytes oldAcc oldCursor loaded inputPrefix rest).
Proof.
  zesu_block.
Qed.

Print Assumptions DesignedBoundary_800d6a14.
