Require Export ZesuSsz.Contracts.DecodeItemCallSpec.
Require Export ZesuSsz.Compliance.DecodeItemUnfoldRegistrations.
Require Import isla.automation.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Export ZesuSsz.Compliance.DecodeItemBranchGuardFacts.
Require Export ZesuSsz.Compliance.DecodeItemCanonicalAnchors.
Require Export ZesuSsz.Compliance.DecodeItemCompletedFoldFacts.
Require Export ZesuSsz.Compliance.DecodeItemCorrectedWitnessSelections.
Require Export ZesuSsz.Compliance.DecodeItemDataWitnessFacts.
Require Export ZesuSsz.Compliance.DecodeItemEntryByteIndexFacts.
Require Export ZesuSsz.Compliance.DecodeItemEntryGuardFacts.
Require Export ZesuSsz.Compliance.DecodeItemFoldBackEdgeWitnesses.
Require Export ZesuSsz.Compliance.DecodeItemFoldExitFacts.
Require Export ZesuSsz.Compliance.DecodeItemFoldInitializationWitnesses.
Require Export ZesuSsz.Compliance.DecodeItemFoldRejectionFacts.
Require Export ZesuSsz.Compliance.DecodeItemFoldSuccessorWitnesses.
Require Export ZesuSsz.Compliance.DecodeItemFoldZeroFacts.
Require Export ZesuSsz.Compliance.DecodeItemHeaderWitnessFacts.
Require Export ZesuSsz.Compliance.DecodeItemInitializationPureFacts.
Require Export ZesuSsz.Compliance.DecodeItemInputHeadWordFacts.
Require Export ZesuSsz.Compliance.DecodeItemLoadedEntryFacts.
Require Export ZesuSsz.Compliance.DecodeItemOutcomeWitnessFacts.
Require Export ZesuSsz.Compliance.DecodeItemOutputBaseWitnessFacts.
Require Export ZesuSsz.Compliance.DecodeItemOutputWitnessSelections.
Require Export ZesuSsz.Compliance.DecodeItemRawOutputFacts.
Require Export ZesuSsz.Compliance.DecodeItemS40GuardFacts.
Require Export ZesuSsz.Compliance.DecodeItemSavedFrameWitnesses.
Require Export ZesuSsz.Compliance.DecodeItemShortListHandoffFacts.
Require Export ZesuSsz.Compliance.DecodeItemStringSuccessorWitnesses.
Require Export ZesuSsz.Compliance.DecodeItemEntryWitnessIntroductions.
Require Export ZesuSsz.Compliance.DecodeItemStoreSelectionIntroductions.
Require Export ZesuSsz.Compliance.DecodeItemMaskedReturnFacts.
Require Export ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.
Require Export ZesuSsz.Compliance.DecodeItemShortListOutputMeaning.
Require Export ZesuSsz.Compliance.DecodeItemEmptyStringOutputMeaning.
Require Export ZesuSsz.Compliance.DecodeItemLongStringOutputMeaning.
Require Export ZesuSsz.Compliance.DecodeItemEntryAdditionalFacts.
Require Export ZesuSsz.Compliance.DecodeItemDataRegistrations.

Global Instance : LithiumUnfold (@decodeItemEntryAt800d698cLiteral) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d698cShortString) := I.
Global Typeclasses Opaque decodeItemEntryAt800d698cLiteral decodeItemEntryAt800d698cShortString.

Global Instance : LithiumUnfold (@decodeItemEntryAt800d698c) := I.
Global Typeclasses Opaque decodeItemEntryAt800d698c.
