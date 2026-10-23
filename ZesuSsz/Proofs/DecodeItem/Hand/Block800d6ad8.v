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

Definition DesignedEntry_800d6ad8
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (loaded : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6ad8 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (loaded) (inputPrefix) (rest)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6ad8) := I.
Global Typeclasses Opaque DesignedEntry_800d6ad8.

Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Lemma DesignedBoundary_800d6ad8 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (loaded : bv 64) (inputPrefix : byte) (rest : list byte)   :
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  instr_pre 0x800d6b08 (∃ (successor_locals : DecodeItemReturnLocals) (successor_inputPrefix : byte) (successor_rest : list byte) (successor_headerLength : Z) (successor_payloadLength : Z), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6b08 (args) (successor_locals) (successor_inputPrefix) (successor_rest) (successor_headerLength) (successor_payloadLength))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6ad8
    (DesignedEntry_800d6ad8 args n payloadStart lengthBytes frameBytes loaded inputPrefix rest).
Proof.
  zesu_block.
Qed.
Print Assumptions DesignedBoundary_800d6ad8.
