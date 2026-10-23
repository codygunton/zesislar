Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Generated.DecodeItem.Entries.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Stock.Closure.index_decodeItem.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import ZesuSsz.Automation.ReturnWand.
Require Import SailStdpp.MachineWord.
From iris.proofmode Require Import environments.

Definition DesignedEntry_800d6a08
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a08 (args) (frameBytes) (x13) (inputPrefix) (rest)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6a08) := I.
Global Typeclasses Opaque DesignedEntry_800d6a08.

Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Local Tactic Notation "hand6a08_recover" integer(count) :=
  do count (ltac2:(Control.focus 1 1 (fun () => ltac1:(zesu_liAStep)))).

Lemma DesignedBoundary_800d6a08 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte)   :
  instr_pre 0x800d6a14 (∃ (successor_n : Z) (successor_payloadStart : Z) (successor_lengthBytes : list byte) (successor_frameBytes : list byte) (successor_oldAcc : bv 64) (successor_oldCursor : bv 64) (successor_loaded : bv 64) (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a14 (args) (successor_n) (successor_payloadStart) (successor_lengthBytes) (successor_frameBytes) (successor_oldAcc) (successor_oldCursor) (successor_loaded) (successor_inputPrefix) (successor_rest))%I -∗
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a08
    (DesignedEntry_800d6a08 args frameBytes x13 inputPrefix rest).
Proof.
  zesu_block.
Qed.
