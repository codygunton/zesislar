Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Compliance.DecodeItemHeaderWitnessFacts.
Require Import ZesuSsz.Compliance.DecodeItemCompletedFoldFacts.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.

Lemma decodeItemEntry6a08Introduction `{!islaG Sigma} `{!threadG}
    args frameBytes (x13 : bv 64) prefix rest :
  decodeItemEntryAt800d6a08 args frameBytes x13 prefix rest ⊢
  ⌜(exists (n payloadStart : Z) (lengthBytes : list byte),
    n = bv_unsigned prefix - 183 /\
    payloadStart = decodeItemInputPointer args + 1 /\
    lengthBytes = firstn (Z.to_nat n) rest /\
    1 <= n <= 8 /\
    decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes)%Z⌝.
Proof.
  unfold decodeItemEntryAt800d6a08.
  iIntros "Hentry".
  iDestruct "Hentry" as (x15 x16) "(%Hfacts & _)".
  iPureIntro. destruct Hfacts as (Hhead & Hclass & Hvalue & Hguard).
  exists (bv_unsigned prefix - 183), (decodeItemInputPointer args + 1),
    (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest).
  unfold decodeItemFoldProvenance. simpl.
  repeat split; try reflexivity; try lia; assumption.
Qed.

Print Assumptions decodeItemEntry6a08Introduction.

Lemma decodeItemEntry6aa8Introduction `{!islaG Sigma} `{!threadG}
    args frameBytes (x13 : bv 64) prefix rest :
  decodeItemEntryAt800d6aa8 args frameBytes x13 prefix rest ⊢
  ⌜(exists (n payloadStart : Z) (lengthBytes : list byte),
    n = bv_unsigned prefix - 247 /\
    payloadStart = decodeItemInputPointer args + 1 /\
    lengthBytes = firstn (Z.to_nat n) rest /\
    1 <= n <= 8 /\
    decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes)%Z⌝.
Proof.
  unfold decodeItemEntryAt800d6aa8.
  iIntros "Hentry".
  iDestruct "Hentry" as (x15 x16) "(%Hfacts & _)".
  iPureIntro. destruct Hfacts as (Hhead & Hclass & Hvalue & Hguard).
  exists (bv_unsigned prefix - 247), (decodeItemInputPointer args + 1),
    (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest).
  unfold decodeItemFoldProvenance. simpl.
  repeat split; try reflexivity; try lia; assumption.
Qed.

Print Assumptions decodeItemEntry6aa8Introduction.

Lemma decodeItemEntry6a38Introduction `{!islaG Sigma} `{!threadG}
    args n payloadStart lengthBytes frameBytes (loaded : bv 64) prefix rest :
  decodeItemEntryAt800d6a38 args n payloadStart lengthBytes frameBytes loaded prefix rest ⊢
  ⌜(exists (headerLength payloadLength : Z),
    headerLength = 1 + n /\ payloadLength = bigEndian lengthBytes /\
    (decodeItemFoldLengthFits args n lengthBytes = true ->
      decodeItemLongAcceptedFacts args false headerLength payloadLength))%Z⌝.
Proof.
  unfold decodeItemEntryAt800d6a38, decodeItemByteFoldResources.
  iIntros "(%Hfacts & Hfold & _)".
  iDestruct "Hfold" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hfold & _)".
  iPureIntro. destruct Hfacts as (Hdomain & Hprovenance & Hframe).
  exists (1 + n), (bigEndian lengthBytes). split; first reflexivity.
  split; first reflexivity. intro Hfits.
  exact (decodeItemCompletedFoldAcceptedWitnessFacts args false prefix rest n
    payloadStart lengthBytes Hdomain Hprovenance (proj2 Hfold) Hfits).
Qed.

Print Assumptions decodeItemEntry6a38Introduction.

Lemma decodeItemEntry6ad8Introduction `{!islaG Sigma} `{!threadG}
    args n payloadStart lengthBytes frameBytes (loaded : bv 64) prefix rest :
  decodeItemEntryAt800d6ad8 args n payloadStart lengthBytes frameBytes loaded prefix rest ⊢
  ⌜(exists (headerLength payloadLength : Z),
    headerLength = 1 + n /\ payloadLength = bigEndian lengthBytes /\
    (decodeItemFoldLengthFits args n lengthBytes = true ->
      decodeItemLongAcceptedFacts args true headerLength payloadLength))%Z⌝.
Proof.
  unfold decodeItemEntryAt800d6ad8, decodeItemByteFoldResources.
  iIntros "(%Hfacts & Hfold & _)".
  iDestruct "Hfold" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hfold & _)".
  iPureIntro. destruct Hfacts as (Hdomain & Hprovenance & Hframe).
  exists (1 + n), (bigEndian lengthBytes). split; first reflexivity.
  split; first reflexivity. intro Hfits.
  exact (decodeItemCompletedFoldAcceptedWitnessFacts args true prefix rest n
    payloadStart lengthBytes Hdomain Hprovenance (proj2 Hfold) Hfits).
Qed.

Print Assumptions decodeItemEntry6ad8Introduction.

