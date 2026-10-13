Require Import ZesuSsz.Automation.All.
From stdpp Require Import bitvector.definitions.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.DecodeItemEmptyStringOutputMeaning.

Lemma decodeItemEmptyStringOutputMeaningConsumer args locals inputPrefix rest :
 decodeItemEmptyStringOutputFacts args locals inputPrefix rest ->
 DecodeMeaningModuloKnownBugs args (decodeItemEmptyStringUpdatedImage locals).
Proof.
 intros HoutputFacts.
 ZesuSsz.Automation.PureFacts.zesu_saturate_derived_facts; assumption.
Qed.

Lemma decodeItemEmptyStringRetainedConsumer args locals inputPrefix rest
 (Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args)
 (HstorageLength : length (returnStorage locals) = 40%nat)
 (Hinput : decodeItemInputHead args inputPrefix rest)
 (Hprefix : bv_unsigned inputPrefix = 128)
 (HstorageBefore : returnStorage locals = decodeItemBeforeStorage args)
 (Haccepted : decodeItemAcceptedFacts args false 1 0) :
 decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
 DecodeMeaningModuloKnownBugs args (decodeItemEmptyStringUpdatedImage locals).
Proof.
 split; first exact Hdomain; assert (HoutputFacts : decodeItemEmptyStringOutputFacts args locals inputPrefix rest) by (unfold decodeItemEmptyStringOutputFacts; repeat first [assumption | split]); ZesuSsz.Automation.PureFacts.zesu_saturate_derived_facts; assumption.
Qed.
