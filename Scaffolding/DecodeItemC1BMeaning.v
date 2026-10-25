Require Import ZesuSsz.Automation.All.
From Coq Require Import List ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Require Import ZesuSsz.Contracts.ResultImage.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Compliance.DecodeItemExitDataFacts.
Require Import ZesuSsz.Compliance.DecodeItemSailIntroduction.
Require Import ZesuSsz.Compliance.DecodeItemSailFold.
Import ListNotations.
Require Import ZesuSsz.Compliance.DecodeItemReturnExitResources.
Open Scope Z_scope.


Lemma decodeItemC1BEncoded args after :
  decodeItemAllowsC1B args after ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after
    (candidateDecodeItem (decodeItemInputBytes args)).
Proof.
  unfold decodeItemAllowsC1B, decodeItemAllows, C1BResult.
  intros (_ & Hresult & _).
  unfold candidateResult40 in Hresult.
  destruct (candidateDecodeItem (decodeItemInputBytes args))
    as [|isList headerLength payloadLength].
  - unfold encodeResult.
    exact (proj2 (decodeItemErrorImageRegistered after) Hresult).
  - apply encodeResult_success_from_padding; first exact Hresult.
    all: destruct Hresult as (_ & _ & _ & _ & _ & _ & _ & _ & Hpreserve).
    all: intros i Hi; apply Hpreserve; lia.
Qed.
Print Assumptions decodeItemC1BEncoded.

Lemma decodeItemRejectedEncodedMeaning args after :
  decodeItemC1BDomain args ->
  decodeItemRejectedFacts args ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after candidateError ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain Hrejected Himage.
  eapply decodeItemErrorPostMeaning; try eassumption.
  unfold encodeResult in Himage. subst after. exact (proj1 errorReturnImage).
Qed.

Local Ltac decodeItemMeaningCase image facts meaning :=
  let Hfacts := fresh "Hfacts" in
  pose proof facts as Hfacts;
  rewrite (proj1 Hfacts) in image;
  eapply meaning; eauto; cbv [MachineWord.MachineWord.Z_idx Z.to_N];
    try lazymatch goal with |- ?lhs < word64Modulus => change (lhs < 18446744073709551616) end; Zify.zify; xlia zchecker.

Lemma decodeItemLongClassMeaning args after (isList : bool) prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  (if isList then 248 <= bv_unsigned prefix <= 255
   else 184 <= bv_unsigned prefix <= 191) ->
  decodeItemAllowsC1B args after -> DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain Hinput Hclass Hallows.
  set (n := bv_unsigned prefix - (if isList then 247 else 183)).
  set (lengthBytes := firstn (Z.to_nat n) rest).
  assert (Hprovenance : decodeItemFoldProvenance args isList prefix rest n
      (decodeItemInputPointer args + 1) lengthBytes).
  { unfold decodeItemFoldProvenance. repeat split; try assumption; reflexivity. }
  assert (Hwidth : 1 <= n <= 8) by (unfold n; destruct isList; simpl in *; lia).
  pose proof (decodeItemC1BEncoded args after Hallows) as Himage.
  destruct (Z_le_gt_dec (1 + n)
    (Z.of_nat (List.length (decodeItemInputBytes args)))) as [Hheader|Hheader].
  - destruct (Z_le_gt_dec ((1 + n + bigEndian lengthBytes) mod word64Modulus)
      (Z.of_nat (List.length (decodeItemInputBytes args)))) as [Hfits|Hreject].
    + pose proof (decodeItemLongAccepted args isList prefix rest n
        (decodeItemInputPointer args + 1) lengthBytes Hdomain Hprovenance Hheader Hfits)
        as Haccepted.
      rewrite (proj1 Haccepted) in Himage.
      pose proof (decodeItemBigEndianNonnegative lengthBytes) as Hpayload.
      destruct isList.
      * eapply decodeItemLongListPostMeaning; eauto; lia.
      * eapply decodeItemLongStringPostMeaning; eauto; lia.
    + pose proof (Z.gt_lt _ _ Hreject) as HrejectLt.
      decodeItemMeaningCase Himage
        (decodeItemLongPayloadRejected args isList prefix rest n
          (decodeItemInputPointer args + 1) lengthBytes Hdomain Hprovenance Hheader HrejectLt)
        decodeItemRejectedEncodedMeaning.
  - pose proof (Z.gt_lt _ _ Hheader) as HheaderLt.
    assert (Hrejected : decodeItemRejectedFacts args).
    { destruct isList.
      - eapply decodeItemLongListHeaderRejected; eauto; unfold n in HheaderLt; exact HheaderLt.
      - eapply decodeItemLongStringHeaderRejected; eauto; unfold n in HheaderLt; exact HheaderLt. }
    rewrite (proj1 Hrejected) in Himage.
    eapply decodeItemRejectedEncodedMeaning; eauto.
Qed.

Lemma decodeItemEmptyInputRejected args :
  decodeItemInputBytes args = [] -> decodeItemRejectedFacts args.
Proof.
  intro Hinput.
  unfold decodeItemRejectedFacts, decodeItemSailCursor.
  rewrite Hinput. split; reflexivity.
Qed.
Print Assumptions decodeItemEmptyInputRejected.

Lemma decodeItemC1BMeaning args after :
  decodeItemC1BDomain args -> decodeItemAllowsC1B args after ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain Hallows.
  pose proof (decodeItemC1BEncoded args after Hallows) as Himage.
  destruct (decodeItemInputBytes args) as [|prefix rest] eqn:Hinput.
  - rewrite <- Hinput in Himage.
    decodeItemMeaningCase Himage (decodeItemEmptyInputRejected args Hinput)
      decodeItemRejectedEncodedMeaning.
  - rewrite <- Hinput in Himage.
    change (decodeItemInputHead args prefix rest) in Hinput.
    assert (Hprefix : 0 <= bv_unsigned prefix <= 255) by bv_solve.
    destruct (Z_le_gt_dec (bv_unsigned prefix) 127) as [Hliteral|Hliteral].
    + decodeItemMeaningCase Himage
        (decodeItemLiteralAccepted args prefix rest Hdomain Hinput Hliteral)
        decodeItemLiteralPostMeaning.
    + destruct (Z.eq_dec (bv_unsigned prefix) 128) as [Hempty|Hempty].
      * decodeItemMeaningCase Himage
          (decodeItemEmptyAccepted args prefix rest Hdomain Hinput Hempty)
          decodeItemEmptyStringPostMeaning.
      * destruct (Z_le_gt_dec (bv_unsigned prefix) 183) as [Hstring|Hstring].
        -- assert (Hclass : 129 <= bv_unsigned prefix <= 183) by lia.
           destruct (Z_le_gt_dec (1 + (bv_unsigned prefix - 128))
             (Z.of_nat (List.length (decodeItemInputBytes args)))) as [Hfits|Hreject].
           ++ decodeItemMeaningCase Himage
                (decodeItemShortStringAccepted args prefix rest Hdomain Hinput Hclass Hfits)
                decodeItemShortStringPostMeaning.
           ++ decodeItemMeaningCase Himage
                (decodeItemShortStringRejected args prefix rest Hdomain Hinput Hclass
                  (Z.gt_lt _ _ Hreject)) decodeItemRejectedEncodedMeaning.
        -- destruct (Z_le_gt_dec (bv_unsigned prefix) 191) as [HlongString|HlongString].
           ++ eapply (decodeItemLongClassMeaning args after false prefix rest); eauto; simpl; lia.
           ++ destruct (Z_le_gt_dec (bv_unsigned prefix) 247) as [Hlist|Hlist].
              ** assert (Hclass : 192 <= bv_unsigned prefix <= 247) by lia.
                 destruct (Z_le_gt_dec (1 + (bv_unsigned prefix - 192))
                   (Z.of_nat (List.length (decodeItemInputBytes args)))) as [Hfits|Hreject].
                 --- decodeItemMeaningCase Himage
                       (decodeItemShortListAccepted args prefix rest Hdomain Hinput Hclass Hfits)
                       decodeItemShortListPostMeaning.
                 --- decodeItemMeaningCase Himage
                       (decodeItemShortListRejected args prefix rest Hdomain Hinput Hclass
                         (Z.gt_lt _ _ Hreject)) decodeItemRejectedEncodedMeaning.
              ** eapply (decodeItemLongClassMeaning args after true prefix rest); eauto; simpl; lia.
Qed.
Print Assumptions decodeItemC1BMeaning.
