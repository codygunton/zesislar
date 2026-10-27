Require Import ZesuSsz.Generated.DecodeItem.Entries.
Require Export ZesuSsz.Contracts.DecodeItemCallSpec.
Require Export ZesuSsz.Generated.DecodeItem.BootstrapRegistrations.
Require Export ZesuSsz.Generated.DecodeItem.Registrations.
Require Import isla.automation.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Export ZesuSsz.Compliance.DecodeItemBranchGuardFacts.
Require Export ZesuSsz.Compliance.DecodeItemCompletedFoldFacts.
Require Export ZesuSsz.Compliance.DecodeItemCorrectedWitnessSelections.
Require Export ZesuSsz.Compliance.DecodeItemDataWitnessFacts.
Require Export ZesuSsz.Compliance.DecodeItemEntryByteIndexFacts.
Require Export ZesuSsz.Compliance.DecodeItemEntryGuardFacts.
Require Export ZesuSsz.Compliance.DecodeItemFoldBackEdgeWitnesses.
Require Export ZesuSsz.Compliance.DecodeItemFoldExitFacts.
Require Export ZesuSsz.Compliance.DecodeItemFoldInitializationWitnesses.
Require Export ZesuSsz.Compliance.DecodeItemFoldRejectionFacts.
Require Export ZesuSsz.Compliance.DecodeItemFoldZeroFacts.
Require Export ZesuSsz.Compliance.DecodeItemHeaderWitnessFacts.
Require Export ZesuSsz.Compliance.DecodeItemInitializationPureFacts.
Require Export ZesuSsz.Compliance.DecodeItemInputHeadWordFacts.
Require Export ZesuSsz.Compliance.DecodeItemLoadedEntryFacts.
Require Export ZesuSsz.Compliance.DecodeItemNormalizedGuardRegistrations.
Require Export ZesuSsz.Compliance.DecodeItemOutcomeWitnessFacts.
Require Export ZesuSsz.Compliance.DecodeItemOutputBaseWitnessFacts.
Require Export ZesuSsz.Compliance.DecodeItemOutputWitnessSelections.
Require Export ZesuSsz.Compliance.DecodeItemRawOutputFacts.
Require Export ZesuSsz.Compliance.DecodeItemS40GuardFacts.
Require Export ZesuSsz.Compliance.DecodeItemSavedFrameWitnesses.
Require Export ZesuSsz.Compliance.DecodeItemShortListHandoffFacts.
Require Export ZesuSsz.Compliance.DecodeItemEntryWitnessIntroductions.
Require Export ZesuSsz.Compliance.DecodeItemStoreSelectionIntroductions.
Require Export ZesuSsz.Compliance.DecodeItemMaskedReturnFacts.
Require Export ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.
Require Export ZesuSsz.Compliance.DecodeItemShortListOutputMeaning.
Require Export ZesuSsz.Compliance.DecodeItemEmptyStringOutputMeaning.
Require Export ZesuSsz.Compliance.DecodeItemLongStringOutputMeaning.
Require Export ZesuSsz.Compliance.DecodeItemEntryAdditionalFacts.
Require Export ZesuSsz.Compliance.DecodeItemDataRegistrations.
Require Export ZesuSsz.Compliance.DecodeItemCanonicalEntryFacts.

(* Derive the source domain and its exact length interval together. *)
#[export] Instance decodeItemDomainAtLengthDerivedFacts
    (returnAddress : Coq.Numbers.BinNums.Z) (args : ZesuSsz.Contracts.RlpDecodeItemContract.DecodeItemArgs) :
  ZesuSsz.Automation.PureFacts.ZesuDerivedFacts
    (ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemDomainAt
      returnAddress ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemC1BDomain args)
    (ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemC1BDomain args /\
     (0 <= ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemInputLength args <
       stdpp.bitvector.definitions.bv_modulus 64%N)%Z).
Proof.
  intro Hdomain.
  exact (Coq.Init.Logic.conj (Coq.Init.Logic.proj2 Hdomain)
    (Coq.Init.Logic.proj2 (Coq.Init.Logic.proj2
      (ZesuSsz.Compliance.DecodeItemFoldRejectionFacts.decodeItemDomainFoldDerivedFacts
        args (Coq.Init.Logic.proj2 Hdomain))))).
Qed.
Print Assumptions decodeItemDomainAtLengthDerivedFacts.
