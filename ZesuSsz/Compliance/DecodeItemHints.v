(* The decodeItem hint umbrella. Since the October retirement it holds only the
   LithiumUnfold instances of contract predicates that the retired October
   registrations (Generated/DecodeItem/BootstrapRegistrations.v) declared and no other
   module declares: decodeItem contracts, its byte-fold contracts, and the parent-header
   contracts that shared that bootstrap. No production module imports it. *)
Require Import isla.automation.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.ParentHeaderLevel1.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Contracts.ParentHeaderSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldSites.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.Level1.IslarisContractSpec) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.Level1.IslarisContractSpec.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.ParentHeaderLevel1.NextUint64InternalHandoffSpec) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.ParentHeaderLevel1.NextUint64InternalHandoffSpec.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.ParentHeaderLevel1.ParentHeaderDirectHandoffSpec) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.ParentHeaderLevel1.ParentHeaderDirectHandoffSpec.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.ParentHeaderLevel1.ParentHeaderTailHandoffSpec) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.ParentHeaderLevel1.ParentHeaderTailHandoffSpec.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemEntryResources) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemEntryResources.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemExitResources) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemExitResources.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.DecodeItemSelected.decodeItemSelectedCode) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.DecodeItemSelected.decodeItemSelectedCode.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.ParentHeaderMemcpyService.ziskMemcpyServiceEntry) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.ParentHeaderMemcpyService.ziskMemcpyServiceEntry.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.ParentHeaderMemcpyService.ziskMemcpyServiceExit) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.ParentHeaderMemcpyService.ziskMemcpyServiceExit.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.ParentHeaderMemcpyService.ziskMemcpyServiceInstrSpec) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.ParentHeaderMemcpyService.ziskMemcpyServiceInstrSpec.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.ParentHeaderMemcpyService.memcpyServicePremise) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.ParentHeaderMemcpyService.memcpyServicePremise.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.ParentHeaderSelected.parentHeaderSelectedCode) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.ParentHeaderSelected.parentHeaderSelectedCode.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.ParentHeaderSelected.parentHeaderSelectedEntry) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.ParentHeaderSelected.parentHeaderSelectedEntry.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.ParentHeaderSelected.parentHeaderSelectedExit) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.ParentHeaderSelected.parentHeaderSelectedExit.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.RlpDecodeItemByteFold.decodeItemByteFoldResources) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.RlpDecodeItemByteFold.decodeItemByteFoldResources.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.RlpDecodeItemByteFold.decodeItemByteFoldStringHeader) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.RlpDecodeItemByteFold.decodeItemByteFoldStringHeader.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.RlpDecodeItemByteFold.decodeItemByteFoldListHeader) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.RlpDecodeItemByteFold.decodeItemByteFoldListHeader.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.RlpDecodeItemByteFoldSites.decodeItemStringFoldAt) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.RlpDecodeItemByteFoldSites.decodeItemStringFoldAt.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.RlpDecodeItemByteFoldSites.decodeItemListFoldAt) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.RlpDecodeItemByteFoldSites.decodeItemListFoldAt.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.decodeItemFoldInitResources) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.decodeItemFoldInitResources.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.decodeItemFoldCheckedResources) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.decodeItemFoldCheckedResources.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.decodeItemFoldEntryObligation) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.decodeItemFoldEntryObligation.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.decodeItemFoldPreservationObligation) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.decodeItemFoldPreservationObligation.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.decodeItemFoldExitObligation) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.decodeItemFoldExitObligation.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.DecodeItemCompositional.decodeItemReturnedCallerRegisters) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.DecodeItemCompositional.decodeItemReturnedCallerRegisters.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.DecodeItemCompositional.decodeItemOtherCallerRegisters) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.DecodeItemCompositional.decodeItemOtherCallerRegisters.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.DecodeItemCompositional.decodeItemOtherCalleeRegisters) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.DecodeItemCompositional.decodeItemOtherCalleeRegisters.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.DecodeItemCompositional.decodeItemUntouchedRegisters) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.DecodeItemCompositional.decodeItemUntouchedRegisters.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.DecodeItemCompositional.decodeItemExitResourcesRegisters) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.DecodeItemCompositional.decodeItemExitResourcesRegisters.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.DecodeItemCompositional.decodeItemEntryResourcesCompositional) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.DecodeItemCompositional.decodeItemEntryResourcesCompositional.

Global Instance : LithiumUnfold (@ZesuSsz.Contracts.DecodeItemCompositional.decodeItemExitResourcesCompositional) := I.
Global Typeclasses Opaque ZesuSsz.Contracts.DecodeItemCompositional.decodeItemExitResourcesCompositional.
