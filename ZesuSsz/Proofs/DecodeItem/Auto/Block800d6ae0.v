Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Generated.DecodeItem.Entries.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Compliance.DecodeItemExitDataFacts.
Require Import ZesuSsz.Compliance.DecodeItemReturnExitResources.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.
Require Import ZesuSsz.Compliance.DecodeItemMaskedReturnFacts.
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
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Automation.ReturnWand.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
From iris.proofmode Require Import environments.

Definition DesignedEntry_800d6ae0
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6ae0 (args) (locals)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6ae0) := I.
Global Typeclasses Opaque DesignedEntry_800d6ae0.

Lemma DesignedBoundary_800d6ae0 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (locals : DecodeItemReturnLocals)  :
  decodeItemSelectedCode -∗
  instr_body 0x800d6ae0
    (DesignedEntry_800d6ae0 args locals).
Proof.
  zesu_block.
Qed.
