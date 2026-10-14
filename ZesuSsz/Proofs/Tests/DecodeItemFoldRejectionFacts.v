Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Compliance.DecodeItemUnfoldRegistrations.
Require Import ZesuSsz.Automation.PureFacts.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.DecodeItemSemanticIntroduction.
Require Import ZesuSsz.Compliance.DecodeItemSailIntroduction.
Open Scope Z_scope.

Require Import ZesuSsz.Compliance.DecodeItemFoldRejectionFacts.

Lemma decodeItemCompletedFoldHint args (isList : bool)
    (inputPrefix : byte) (rest : list byte) (n payloadStart : Z)
    (lengthBytes : list byte) :
  decodeItemC1BDomain args ->
  decodeItemFoldProvenance args isList inputPrefix rest n payloadStart lengthBytes ->
  decodeItemByteFoldFacts args n n payloadStart lengthBytes ->
  decodeItemFoldLengthFits args n lengthBytes = false ->
  SimplAnd (decodeItemRejectedFacts args) True.
Proof.
  intros Hdomain Hprovenance Hfold Hfits.
  typeclasses eauto.
Qed.
Print Assumptions decodeItemCompletedFoldHint.
