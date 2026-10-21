Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Common.
Require Import ZesuSsz.Compliance.DecodeItemShortListOutputMeaning.
Require Import ZesuSsz.Compliance.DecodeItemReturnExitResources.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Compliance.DecodeItemExitDataFacts.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Require Import ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.
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

Definition DesignedEntry_800d6a78
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ((ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6a78 (args) (locals) (inputPrefix) (rest)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6a78) := I.
Global Typeclasses Opaque DesignedEntry_800d6a78.

Lemma DesignedBoundary_800d6a78 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte)  :
  decodeItemSelectedCode -∗
  instr_body 0x800d6a78
    (DesignedEntry_800d6a78 args locals inputPrefix rest).
Proof.
  zesu_block.
Qed.
