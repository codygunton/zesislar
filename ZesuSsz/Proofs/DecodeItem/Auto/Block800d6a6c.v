Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Generated.DecodeItem.Entries.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.isla.
Require Import ZesuSsz.Stock.Closure.index_decodeItem.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Automation.ReturnWand.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
From iris.proofmode Require Import environments.

Definition DesignedEntry_800d6a6c
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a6c (args) (frameBytes) (x13) (inputPrefix) (rest)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6a6c) := I.
Global Typeclasses Opaque DesignedEntry_800d6a6c.

Lemma DesignedBoundary_800d6a6c `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte)   :
  instr_pre 0x800d6a78 (∃ (successor_locals : DecodeItemReturnLocals) (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a78 (args) (successor_locals) (successor_inputPrefix) (successor_rest))%I -∗
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a6c
    (DesignedEntry_800d6a6c args frameBytes x13 inputPrefix rest).
Proof.
  zesu_block.
Qed.

Print Assumptions DesignedBoundary_800d6a6c.
