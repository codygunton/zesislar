Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Proofs.DecodeItem.ByteFoldPure.
From Coq Require Import List ZArith.
Open Scope Z_scope.

Lemma decodeItemHeader6a24Step `{!islaG Sigma} `{!threadG}
    args n i payloadStart lengthBytes frameBytes (loaded : bv 64) :
  decodeItemByteFoldStringHeader args n i payloadStart lengthBytes frameBytes loaded ⊢
  ⌜(forall next : byte, i < n ->
    nth_error lengthBytes (Z.to_nat i) = Some next ->
    decodeItemByteFoldFacts args n (i + 1) payloadStart lengthBytes /\
    bigEndian (firstn (Z.to_nat (i + 1)) lengthBytes) =
      256 * bigEndian (firstn (Z.to_nat i) lengthBytes) + bv_unsigned next)%Z⌝.
Proof.
  unfold decodeItemByteFoldStringHeader, decodeItemByteFoldResources.
  iIntros "Hheader".
  iDestruct "Hheader" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hfacts & _)".
  iPureIntro. intros next Hguard Hnext.
  exact (decodeItem_fold_preservation args n i payloadStart lengthBytes next
    (proj2 Hfacts) Hguard Hnext).
Qed.


Lemma decodeItemHeader6ac4Step `{!islaG Sigma} `{!threadG}
    args n i payloadStart lengthBytes frameBytes (loaded : bv 64) :
  decodeItemByteFoldListHeader args n i payloadStart lengthBytes frameBytes loaded ⊢
  ⌜(forall next : byte, i < n ->
    nth_error lengthBytes (Z.to_nat i) = Some next ->
    decodeItemByteFoldFacts args n (i + 1) payloadStart lengthBytes /\
    bigEndian (firstn (Z.to_nat (i + 1)) lengthBytes) =
      256 * bigEndian (firstn (Z.to_nat i) lengthBytes) + bv_unsigned next)%Z⌝.
Proof.
  unfold decodeItemByteFoldListHeader, decodeItemByteFoldResources.
  iIntros "Hheader".
  iDestruct "Hheader" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hfacts & _)".
  iPureIntro. intros next Hguard Hnext.
  exact (decodeItem_fold_preservation args n i payloadStart lengthBytes next
    (proj2 Hfacts) Hguard Hnext).
Qed.
