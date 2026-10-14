Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.
Require Import ZesuSsz.Automation.PureFacts.
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
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.

Definition DesignedEntry_800d697c
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ((ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d697c (args) (frameBytes) (x13) (inputPrefix) (rest)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d697c) := I.
Global Typeclasses Opaque DesignedEntry_800d697c.

Local Tactic Notation "hand697c_recover" integer(count) := do count zesu_liAStep.

Lemma DesignedBoundary_800d697c `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte)  :
  instr_pre 0x800d698c (∃ (successor_locals : DecodeItemReturnLocals) (successor_pointerBytes : list byte) (successor_lengthBytes : list byte) (successor_inputPrefix : byte) (successor_rest : list byte) (successor_isLiteral : bool), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d698c (args) (successor_locals) (successor_pointerBytes) (successor_lengthBytes) (successor_inputPrefix) (successor_rest) (successor_isLiteral))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d697c
    (DesignedEntry_800d697c args frameBytes x13 inputPrefix rest).
Proof.
zesu_block.
Qed.
