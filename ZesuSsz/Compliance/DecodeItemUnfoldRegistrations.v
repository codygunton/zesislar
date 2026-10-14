Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.ParentHeaderLevel1.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Contracts.NextUint64Selected.
Require Import ZesuSsz.Contracts.ParentHeaderSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldSites.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemErrorBranch.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemJoinTransfers.

(* Expose the input boundary before register-column lookup. *)
Global Hint Unfold decodeItemSysRegs : regcol_compute_unfold.

Global Typeclasses Opaque IslarisContractSpec.
Global Instance : LithiumUnfold (@IslarisContractSpec) := I.
Global Typeclasses Opaque NextUint64InternalHandoffSpec
  ParentHeaderDirectHandoffSpec ParentHeaderTailHandoffSpec.
Global Instance : LithiumUnfold (@NextUint64InternalHandoffSpec) := I.
Global Instance : LithiumUnfold (@ParentHeaderDirectHandoffSpec) := I.
Global Instance : LithiumUnfold (@ParentHeaderTailHandoffSpec) := I.
Global Typeclasses Opaque decodeItemEntryResources decodeItemExitResources.
Global Instance : LithiumUnfold (@decodeItemEntryResources) := I.
Global Instance : LithiumUnfold (@decodeItemExitResources) := I.
Global Typeclasses Opaque decodeItemSelectedCode.
Global Instance : LithiumUnfold (@decodeItemSelectedCode) := I.
Global Typeclasses Opaque ziskMemcpyServiceEntry ziskMemcpyServiceExit
  ziskMemcpyServiceInstrSpec memcpyServicePremise.
Global Instance : LithiumUnfold (@ziskMemcpyServiceEntry) := I.
Global Instance : LithiumUnfold (@ziskMemcpyServiceExit) := I.
Global Instance : LithiumUnfold (@ziskMemcpyServiceInstrSpec) := I.
Global Instance : LithiumUnfold (@memcpyServicePremise) := I.
Global Typeclasses Opaque nextUint64SelectedCode nextUint64SelectedEntry
  nextUint64SelectedExit parentHeaderSelectedCode
  parentHeaderSelectedEntry parentHeaderSelectedExit.
Global Instance : LithiumUnfold (@nextUint64SelectedCode) := I.
Global Instance : LithiumUnfold (@nextUint64SelectedEntry) := I.
Global Instance : LithiumUnfold (@nextUint64SelectedExit) := I.
Global Instance : LithiumUnfold (@parentHeaderSelectedCode) := I.
Global Instance : LithiumUnfold (@parentHeaderSelectedEntry) := I.
Global Instance : LithiumUnfold (@parentHeaderSelectedExit) := I.
Global Typeclasses Opaque decodeItemByteFoldResources
  decodeItemByteFoldStringHeader decodeItemByteFoldListHeader.
Global Instance : LithiumUnfold (@decodeItemByteFoldResources) := I.
Global Instance : LithiumUnfold (@decodeItemByteFoldStringHeader) := I.
Global Instance : LithiumUnfold (@decodeItemByteFoldListHeader) := I.
Global Typeclasses Opaque decodeItemStringFoldAt decodeItemListFoldAt.
Global Instance : LithiumUnfold (@decodeItemStringFoldAt) := I.
Global Instance : LithiumUnfold (@decodeItemListFoldAt) := I.
Global Typeclasses Opaque decodeItemFoldInitResources
  decodeItemFoldCheckedResources decodeItemFoldEntryObligation
  decodeItemFoldPreservationObligation decodeItemFoldExitObligation.
Global Instance : LithiumUnfold (@decodeItemFoldInitResources) := I.
Global Instance : LithiumUnfold (@decodeItemFoldCheckedResources) := I.
Global Instance : LithiumUnfold (@decodeItemFoldEntryObligation) := I.
Global Instance : LithiumUnfold (@decodeItemFoldPreservationObligation) := I.
Global Instance : LithiumUnfold (@decodeItemFoldExitObligation) := I.
Global Typeclasses Opaque decodeItemEntryAt800d6a24
  decodeItemEntryAt800d6ac4 decodeItemBodyAt800d6a24
  decodeItemBodyAt800d6ac4.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6a24) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6ac4) := I.
Global Instance : LithiumUnfold (@decodeItemBodyAt800d6a24) := I.
Global Instance : LithiumUnfold (@decodeItemBodyAt800d6ac4) := I.
Global Typeclasses Opaque decodeItemBranchContinuationAt
  decodeItemBranchContinuation decodeItemBranchBase
  decodeItemEntryAt800d6974 decodeItemEntryAt800d697c
  decodeItemEntryAt800d69a4 decodeItemEntryAt800d69d8
  decodeItemEntryAt800d69e0 decodeItemEntryAt800d69e8
  decodeItemEntryAt800d6a00 decodeItemEntryAt800d6a08
  decodeItemEntryAt800d6a14 decodeItemEntryAt800d6a38
  decodeItemEntryAt800d6a64 decodeItemEntryAt800d6a6c
  decodeItemEntryAt800d6aa8 decodeItemEntryAt800d6ab4
  decodeItemEntryAt800d6ad8.
Global Instance : LithiumUnfold (@decodeItemBranchContinuationAt) := I.
Global Instance : LithiumUnfold (@decodeItemBranchContinuation) := I.
Global Instance : LithiumUnfold (@decodeItemBranchBase) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6974) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d697c) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d69a4) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d69d8) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d69e0) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d69e8) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6a00) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6a08) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6a14) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6a38) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6a64) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6a6c) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6aa8) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6ab4) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6ad8) := I.
Global Typeclasses Opaque decodeItemReturnEntryCore
  decodeItem698cCaseResources decodeItemEntryAt800d69b0
  decodeItemEntryAt800d6a40 decodeItemEntryAt800d6a78
  decodeItemEntryAt800d6ae0 decodeItemEntryAt800d6b08
  decodeItemReturnOkExit decodeItemReturnErrorExit
  decodeItemReturnBlockObligation
  decodeItemReturnAt800d698c decodeItemReturnAt800d69b0
  decodeItemReturnAt800d6a40 decodeItemReturnAt800d6a78
  decodeItemReturnAt800d6ae0 decodeItemReturnAt800d6b08.
Global Instance : LithiumUnfold (@decodeItemReturnEntryCore) := I.
Global Instance : LithiumUnfold (@decodeItem698cCaseResources) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d69b0) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6a40) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6a78) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6ae0) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6b08) := I.
Global Instance : LithiumUnfold (@decodeItemReturnOkExit) := I.
Global Instance : LithiumUnfold (@decodeItemReturnErrorExit) := I.
Global Instance : LithiumUnfold (@decodeItemReturnBlockObligation) := I.
Global Instance : LithiumUnfold (@decodeItemReturnAt800d698c) := I.
Global Instance : LithiumUnfold (@decodeItemReturnAt800d69b0) := I.
Global Instance : LithiumUnfold (@decodeItemReturnAt800d6a40) := I.
Global Instance : LithiumUnfold (@decodeItemReturnAt800d6a78) := I.
Global Instance : LithiumUnfold (@decodeItemReturnAt800d6ae0) := I.
Global Instance : LithiumUnfold (@decodeItemReturnAt800d6b08) := I.
Global Typeclasses Opaque decodeItemJoinTransferObligation
  decodeItemJoin698cTarget decodeItemJoin6ae0Target
  decodeItemJoin698cFrom697c decodeItemJoin698cFrom69e8
  decodeItemJoin6a24From6a14 decodeItemJoin6a24Backedge
  decodeItemJoin6ac4From6ab4 decodeItemJoin6ac4Backedge
  decodeItemJoin6ae0From6970 decodeItemJoin6ae0From69e0
  decodeItemJoin6ae0From6a08 decodeItemJoin6ae0From6a38
  decodeItemJoin6ae0From6a6c decodeItemJoin6ae0From6aa8
  decodeItemJoin6ae0From6ad8.
Global Instance : LithiumUnfold (@decodeItemJoinTransferObligation) := I.
Global Instance : LithiumUnfold (@decodeItemJoin698cTarget) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6ae0Target) := I.
Global Instance : LithiumUnfold (@decodeItemJoin698cFrom697c) := I.
Global Instance : LithiumUnfold (@decodeItemJoin698cFrom69e8) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6a24From6a14) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6a24Backedge) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6ac4From6ab4) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6ac4Backedge) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6ae0From6970) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6ae0From69e0) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6ae0From6a08) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6ae0From6a38) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6ae0From6a6c) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6ae0From6aa8) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6ae0From6ad8) := I.
Global Typeclasses Opaque decodeItemErrorBranchEntry.
Global Instance : LithiumUnfold (@decodeItemErrorBranchEntry) := I.

