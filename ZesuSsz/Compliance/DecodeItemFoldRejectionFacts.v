Require Import ZesuSsz.Automation.All.
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

Lemma decodeItemCompletedFoldRejected args (isList : bool)
    (inputPrefix : byte) (rest : list byte) (n payloadStart : Z)
    (lengthBytes : list byte) :
  decodeItemC1BDomain args ->
  decodeItemFoldProvenance args isList inputPrefix rest n payloadStart lengthBytes ->
  decodeItemByteFoldFacts args n n payloadStart lengthBytes ->
  decodeItemFoldLengthFits args n lengthBytes = false ->
  decodeItemRejectedFacts args.
Proof.
  intros Hdomain Hprovenance Hfold Hfits.
  pose proof (decodeItemDomainInputLengthBounds args Hdomain) as Hbounds.
  assert (Hrange : 0 <= decodeItemInputLength args < bv_modulus 64) by
    (unfold word64Modulus in *; change (0 <= decodeItemInputLength args < 2^64); lia).
  pose proof Hdomain as Hfacts.
  destruct Hfacts as (Hinput & Hstorage & Hlayout).
  eapply (decodeItemLongPayloadRejected args isList inputPrefix rest n payloadStart lengthBytes);
    [exact Hdomain | exact Hprovenance | |].
  - unfold decodeItemByteFoldFacts in Hfold. rewrite -Hinput. lia.
  - unfold decodeItemFoldLengthFits in Hfits. apply Z.leb_gt in Hfits.
    rewrite (Z_to_bv_small 64 _ Hrange) Z_to_bv_unsigned in Hfits.
    rewrite -Hinput. unfold word64Modulus.
    replace (1 + n + bigEndian lengthBytes) with (bigEndian lengthBytes + n + 1) by ring.
    exact Hfits.
Qed.
Print Assumptions decodeItemCompletedFoldRejected.

#[export] Instance decodeItemDomainFoldDerivedFacts args :
  ZesuDerivedFacts (decodeItemC1BDomain args)
    (decodeItemInputLength args = Z.of_nat (length (decodeItemInputBytes args)) /\
     length (decodeItemBeforeStorage args) = 40%nat /\
     0 <= decodeItemInputLength args < bv_modulus 64).
Proof.
  intros Hdomain.
  pose proof (decodeItemDomainInputLengthBounds args Hdomain) as Hbounds.
  destruct Hdomain as (Hinput & Hstorage & Hlayout).
  split; [exact Hinput |]. split; [exact Hstorage |].
  unfold word64Modulus in *. change (0 <= decodeItemInputLength args < 2^64). lia.
Qed.
Print Assumptions decodeItemDomainFoldDerivedFacts.
