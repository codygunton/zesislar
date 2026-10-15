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

Require Import ZesuSsz.Compliance.DecodeItemCorrectedWitnessSelections.
Lemma decodeItemEntry6a08Introduction `{!islaG Sigma} `{!threadG}
    args frameBytes (x13 : bv 64) prefix rest :
  decodeItemEntryAt800d6a08 args frameBytes x13 prefix rest ⊢
  ⌜(exists (n payloadStart : Z) (lengthBytes : list byte),
    (n = bv_unsigned prefix - 183 /\
    payloadStart = decodeItemInputPointer args + 1 /\
    lengthBytes = firstn (Z.to_nat n) rest /\
    1 <= n <= 8 /\
    decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes) /\
    decodeItemC1BDomain args /\
    decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
    decodeItemSavedFrameFacts args frameBytes)%Z⌝.
Proof.
  unfold decodeItemEntryAt800d6a08.
  iIntros "Hentry".
  iDestruct "Hentry" as (x15 x16) "(%Hfacts & H13 & H14 & H15 & H16 & Hbase)".
  iEval (unfold decodeItemBranchBase) in "Hbase".
  iDestruct "Hbase" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hbase & _)".
  iPureIntro. destruct Hfacts as (Hhead & Hclass & Hvalue & Hguard).
  exists (bv_unsigned prefix - 183), (decodeItemInputPointer args + 1),
    (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest).
  split.
  { unfold decodeItemFoldProvenance. simpl.
    repeat split; try reflexivity; try lia; assumption. }
  pose proof (proj2 (proj2 Hbase)) as Hdomain.
  exact (conj Hdomain (conj (conj eq_refl Hdomain) (proj1 Hbase))).
Qed.
Print Assumptions decodeItemEntry6a08Introduction.

Lemma decodeItemEntry6aa8Introduction `{!islaG Sigma} `{!threadG}
    args frameBytes (x13 : bv 64) prefix rest :
  decodeItemEntryAt800d6aa8 args frameBytes x13 prefix rest ⊢
  ⌜(exists (n payloadStart : Z) (lengthBytes : list byte),
    (n = bv_unsigned prefix - 247 /\
    payloadStart = decodeItemInputPointer args + 1 /\
    lengthBytes = firstn (Z.to_nat n) rest /\
    1 <= n <= 8 /\
    decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes) /\
    decodeItemC1BDomain args /\
    decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
    decodeItemSavedFrameFacts args frameBytes)%Z⌝.
Proof.
  unfold decodeItemEntryAt800d6aa8.
  iIntros "Hentry".
  iDestruct "Hentry" as (x15 x16) "(%Hfacts & H13 & H14 & H15 & H16 & Hbase)".
  iEval (unfold decodeItemBranchBase) in "Hbase".
  iDestruct "Hbase" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hbase & _)".
  iPureIntro. destruct Hfacts as (Hhead & Hclass & Hvalue & Hguard).
  exists (bv_unsigned prefix - 247), (decodeItemInputPointer args + 1),
    (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest).
  split.
  { unfold decodeItemFoldProvenance. simpl.
    repeat split; try reflexivity; try lia; assumption. }
  pose proof (proj2 (proj2 Hbase)) as Hdomain.
  exact (conj Hdomain (conj (conj eq_refl Hdomain) (proj1 Hbase))).
Qed.
Print Assumptions decodeItemEntry6aa8Introduction.

Lemma decodeItemEntry6a38Introduction `{!islaG Sigma} `{!threadG}
    args n payloadStart lengthBytes frameBytes (loaded : bv 64) prefix rest :
  decodeItemEntryAt800d6a38 args n payloadStart lengthBytes frameBytes loaded prefix rest ⊢
  ⌜(exists (headerLength payloadLength : Z),
    (headerLength = 1 + n /\ payloadLength = bigEndian lengthBytes /\
    (decodeItemFoldLengthFits args n lengthBytes = true ->
      decodeItemLongAcceptedFacts args false headerLength payloadLength)) /\
    decodeItemC1BDomain args /\
    decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
    decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes /\
    decodeItemSavedFrameFacts args frameBytes /\
    decodeItemByteFoldFacts args n n payloadStart lengthBytes /\
    decodeItemInputHead args prefix rest /\ 184 <= bv_unsigned prefix <= 191 /\
    n = bv_unsigned prefix - 183 /\ payloadStart = decodeItemInputPointer args + 1 /\
    lengthBytes = firstn (Z.to_nat n) rest /\
    (~ bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) <
    bv_signed (bv_zero_extend 128
      (Z_to_bv 64 (bigEndian (take (Z.to_nat n) lengthBytes)) + Z_to_bv 64 (n + 1))) ->
      decodeItemFoldLengthFits args n lengthBytes = true) /\
    0 <= payloadLength < word64Modulus /\
    bv_unsigned (Z_to_bv 64 (payloadStart + n)) = decodeItemInputPointer args + headerLength /\
    bv_unsigned (Z_to_bv 64 (bigEndian lengthBytes)) = payloadLength /\
    bv_unsigned (Z_to_bv 64 (bigEndian lengthBytes + n + 1)) =
      ((headerLength + payloadLength) mod word64Modulus))%Z⌝.
Proof.
  unfold decodeItemEntryAt800d6a38, decodeItemByteFoldResources.
  iIntros "(%Hfacts & Hfold & _)".
  iDestruct "Hfold" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hfold & _)".
  iPureIntro. destruct Hfacts as (Hdomain & Hprovenance & Hframe).
  assert (Hcanonical : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args)
    by exact (conj eq_refl Hdomain).
  pose proof (proj2 Hfold) as Hcompleted.
  pose proof (decodeItemCompletedFoldValueBounds args n payloadStart lengthBytes Hcompleted) as Hbounds.
  pose proof (decodeItemCompletedFoldWordValues args n payloadStart lengthBytes Hdomain Hcompleted) as Hwords.
  pose proof (decodeItemCompletedFoldFitsGuard args n payloadStart lengthBytes Hcompleted) as HguardRoute.
  pose proof Hprovenance as Hlayout. unfold decodeItemFoldProvenance in Hlayout. simpl in Hlayout.
  destruct Hlayout as (Hhead & Hclass & Hn & Hstart & Hbytes).
  exists (1 + n), (bigEndian lengthBytes). split.
  { split; first reflexivity. split; first reflexivity. intro Hfits.
    exact (decodeItemCompletedFoldAcceptedWitnessFacts args false prefix rest n
      payloadStart lengthBytes Hdomain Hprovenance Hcompleted Hfits). }
  exact (conj Hdomain (conj Hcanonical (conj Hprovenance (conj Hframe (conj Hcompleted
    (conj Hhead (conj Hclass (conj Hn (conj Hstart (conj Hbytes (conj HguardRoute (conj Hbounds Hwords)))))))))))).
Qed.
Print Assumptions decodeItemEntry6a38Introduction.

Lemma decodeItemEntry6ad8Introduction `{!islaG Sigma} `{!threadG}
    args n payloadStart lengthBytes frameBytes (loaded : bv 64) prefix rest :
  decodeItemEntryAt800d6ad8 args n payloadStart lengthBytes frameBytes loaded prefix rest ⊢
  ⌜(exists (headerLength payloadLength : Z),
    (headerLength = 1 + n /\ payloadLength = bigEndian lengthBytes /\
    (decodeItemFoldLengthFits args n lengthBytes = true ->
      decodeItemLongAcceptedFacts args true headerLength payloadLength)) /\
    decodeItemC1BDomain args /\
    decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
    decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes /\
    decodeItemSavedFrameFacts args frameBytes /\
    decodeItemByteFoldFacts args n n payloadStart lengthBytes /\
    decodeItemInputHead args prefix rest /\ 248 <= bv_unsigned prefix <= 255 /\
    n = bv_unsigned prefix - 247 /\ payloadStart = decodeItemInputPointer args + 1 /\
    lengthBytes = firstn (Z.to_nat n) rest /\
    (bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) >=
    bv_signed (bv_zero_extend 128
      (Z_to_bv 64 (bigEndian (take (Z.to_nat n) lengthBytes)) + Z_to_bv 64 (n + 1))) ->
      decodeItemFoldLengthFits args n lengthBytes = true) /\
    0 <= payloadLength < word64Modulus /\
    bv_unsigned (Z_to_bv 64 (payloadStart + n)) = decodeItemInputPointer args + headerLength /\
    bv_unsigned (Z_to_bv 64 (bigEndian lengthBytes)) = payloadLength /\
    bv_unsigned (Z_to_bv 64 (bigEndian lengthBytes + n + 1)) =
      ((headerLength + payloadLength) mod word64Modulus))%Z⌝.
Proof.
  unfold decodeItemEntryAt800d6ad8, decodeItemByteFoldResources.
  iIntros "(%Hfacts & Hfold & _)".
  iDestruct "Hfold" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hfold & _)".
  iPureIntro. destruct Hfacts as (Hdomain & Hprovenance & Hframe).
  assert (Hcanonical : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args)
    by exact (conj eq_refl Hdomain).
  pose proof (proj2 Hfold) as Hcompleted.
  pose proof (decodeItemCompletedFoldValueBounds args n payloadStart lengthBytes Hcompleted) as Hbounds.
  pose proof (decodeItemCompletedFoldWordValues args n payloadStart lengthBytes Hdomain Hcompleted) as Hwords.
  assert (HguardRoute : (bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) >=
    bv_signed (bv_zero_extend 128
      (Z_to_bv 64 (bigEndian (take (Z.to_nat n) lengthBytes)) + Z_to_bv 64 (n + 1))) ->
      decodeItemFoldLengthFits args n lengthBytes = true)).
  { intro Hguard. apply (decodeItemCompletedFoldFitsGuard args n payloadStart lengthBytes Hcompleted).
    apply Z.le_ngt. apply Z.ge_le. exact Hguard. }
  pose proof Hprovenance as Hlayout. unfold decodeItemFoldProvenance in Hlayout. simpl in Hlayout.
  destruct Hlayout as (Hhead & Hclass & Hn & Hstart & Hbytes).
  exists (1 + n), (bigEndian lengthBytes). split.
  { split; first reflexivity. split; first reflexivity. intro Hfits.
    exact (decodeItemCompletedFoldAcceptedWitnessFacts args true prefix rest n
      payloadStart lengthBytes Hdomain Hprovenance Hcompleted Hfits). }
  exact (conj Hdomain (conj Hcanonical (conj Hprovenance (conj Hframe (conj Hcompleted
    (conj Hhead (conj Hclass (conj Hn (conj Hstart (conj Hbytes (conj HguardRoute (conj Hbounds Hwords)))))))))))).
Qed.
Print Assumptions decodeItemEntry6ad8Introduction.
