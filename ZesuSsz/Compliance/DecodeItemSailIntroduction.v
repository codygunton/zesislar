Require Import ZesuSsz.Automation.All.
From Coq Require Import List ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types EvmSailRlp.evm_rlp.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.SailRun.
Require Import ZesuSsz.Compliance.DecodeItemSailEvaluation.
Require Import ZesuSsz.Compliance.DecodeItemSemanticIntroduction.
Require Import ZesuSsz.Compliance.DecodeItemSailFold.
Import ListNotations.
Open Scope Z_scope.

Lemma decodeItemSailSuccessFromPrompt args isList headerLength payloadLength :
  decodeItemC1BDomain args ->
  (exists fullLength contentLength (field : RlpFieldRef 0 fullLength contentLength),
    runPrompt (EvmSailRlp.evm_rlp.rlp_decode_item (decodeItemSailCursor args))
      (decodeItemInstalledState (decodeItemInputBytes args)) true =
      (Success (@existT Z (fun full => {content : Z & RlpFieldRef 0 full content})
        fullLength (@existT Z (fun content => RlpFieldRef 0 fullLength content)
          contentLength field)), decodeItemInstalledState (decodeItemInputBytes args)) /\
    RlpFieldRef_is_list field = isList /\
    fullLength - contentLength = headerLength /\ contentLength = payloadLength) ->
  decodeItemSailSuccess args isList headerLength payloadLength.
Proof.
  intros Hdomain [fullLength [contentLength [field [Hrun Hfacts]]]].
  exists fullLength, contentLength, field. split; last exact Hfacts.
  unfold runRlpDecodeItem, SailRun.runDecoder.
  rewrite (decodeItemSailInputSliceValid args Hdomain).
  unfold SailStdpp.Prompt_monad.bind0.
  erewrite decodeItemRunPromptBindSuccess with (value := tt)
    (rs' := decodeItemInstalledState (decodeItemInputBytes args));
    last apply decodeItemRunPromptInitialized.
  rewrite Hrun. reflexivity.
Qed.

Lemma decodeItemLiteralSailSuccess args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  bv_unsigned prefix <= 127 -> decodeItemSailSuccess args false 0 1.
Proof.
  intros Hdomain Hinput Hclass.
  apply decodeItemSailSuccessFromPrompt; first exact Hdomain.
  unfold decodeItemInputHead in Hinput. unfold decodeItemSailCursor. rewrite Hinput.
  eapply decodeItemRunPromptAcceptedHeader; try reflexivity; try (simpl; lia).
  apply decodeItemRunPromptLiteralHeader; try reflexivity;
    auto using decodeItemInstalledBytes.
Qed.

Lemma decodeItemEmptySailSuccess args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  bv_unsigned prefix = 128 -> decodeItemSailSuccess args false 1 0.
Proof.
  intros Hdomain Hinput Hclass.
  apply decodeItemSailSuccessFromPrompt; first exact Hdomain.
  unfold decodeItemInputHead in Hinput. unfold decodeItemSailCursor. rewrite Hinput.
  eapply decodeItemRunPromptAcceptedHeader; try reflexivity; try (simpl; lia).
  match goal with
  | |- runPrompt (EvmSailRlp.evm_rlp.rlp_ref_hdr ?slice) ?rs true = _ =>
      pose proof (decodeItemRunPromptShortStringHeader prefix rest rs slice
        (decodeItemInstalledBytes _) eq_refl ltac:(lia)) as Hheader
  end.
  rewrite Hclass in Hheader. exact Hheader.
Qed.

Lemma decodeItemShortStringSailSuccess args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  129 <= bv_unsigned prefix <= 183 ->
  1 + (bv_unsigned prefix - 128) <= Z.of_nat (List.length (decodeItemInputBytes args)) ->
  decodeItemSailSuccess args false 1 (bv_unsigned prefix - 128).
Proof.
  intros Hdomain Hinput Hclass Hfits.
  apply decodeItemSailSuccessFromPrompt; first exact Hdomain.
  unfold decodeItemInputHead in Hinput. rewrite Hinput in Hfits.
  unfold decodeItemSailCursor. rewrite Hinput.
  eapply decodeItemRunPromptAcceptedHeader; try reflexivity; try lia.
  all: try exact Hfits.
  apply decodeItemRunPromptShortStringHeader; try reflexivity;
    auto using decodeItemInstalledBytes; lia.
Qed.

Lemma decodeItemShortListSailSuccess args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  192 <= bv_unsigned prefix <= 247 ->
  1 + (bv_unsigned prefix - 192) <= Z.of_nat (List.length (decodeItemInputBytes args)) ->
  decodeItemSailSuccess args true 1 (bv_unsigned prefix - 192).
Proof.
  intros Hdomain Hinput Hclass Hfits.
  apply decodeItemSailSuccessFromPrompt; first exact Hdomain.
  unfold decodeItemInputHead in Hinput. rewrite Hinput in Hfits.
  unfold decodeItemSailCursor. rewrite Hinput.
  eapply decodeItemRunPromptAcceptedHeader; try reflexivity; try lia.
  all: try exact Hfits.
  apply decodeItemRunPromptShortListHeader; try reflexivity;
    auto using decodeItemInstalledBytes; lia.
Qed.

Print Assumptions decodeItemSailSuccessFromPrompt.
Print Assumptions decodeItemLiteralSailSuccess.
Print Assumptions decodeItemEmptySailSuccess.
Print Assumptions decodeItemShortStringSailSuccess.
Print Assumptions decodeItemShortListSailSuccess.

Lemma decodeItemLiteralAccepted args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  bv_unsigned prefix <= 127 -> decodeItemAcceptedFacts args false 0 1.
Proof.
  intros Hdomain Hinput Hclass. split.
  - eapply decodeItemLiteralCandidateIntro; eauto.
  - eapply decodeItemLiteralSailSuccess; eauto.
Qed.

Lemma decodeItemEmptyAccepted args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  bv_unsigned prefix = 128 -> decodeItemAcceptedFacts args false 1 0.
Proof.
  intros Hdomain Hinput Hclass. split.
  - eapply decodeItemEmptyCandidateIntro; eauto.
  - eapply decodeItemEmptySailSuccess; eauto.
Qed.

Lemma decodeItemShortStringAccepted args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  129 <= bv_unsigned prefix <= 183 ->
  1 + (bv_unsigned prefix - 128) <= Z.of_nat (List.length (decodeItemInputBytes args)) ->
  decodeItemAcceptedFacts args false 1 (bv_unsigned prefix - 128).
Proof.
  intros Hdomain Hinput Hclass Hfits. split.
  - eapply decodeItemShortStringCandidateIntro; eauto.
    rewrite Z.mod_small; first exact Hfits. unfold word64Modulus. lia.
  - eapply decodeItemShortStringSailSuccess; eauto.
Qed.

Lemma decodeItemShortListAccepted args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  192 <= bv_unsigned prefix <= 247 ->
  1 + (bv_unsigned prefix - 192) <= Z.of_nat (List.length (decodeItemInputBytes args)) ->
  decodeItemAcceptedFacts args true 1 (bv_unsigned prefix - 192).
Proof.
  intros Hdomain Hinput Hclass Hfits. split.
  - eapply decodeItemShortListCandidateIntro; eauto.
    rewrite Z.mod_small; first exact Hfits. unfold word64Modulus. lia.
  - eapply decodeItemShortListSailSuccess; eauto.
Qed.

Print Assumptions decodeItemLiteralAccepted.
Print Assumptions decodeItemEmptyAccepted.
Print Assumptions decodeItemShortStringAccepted.
Print Assumptions decodeItemShortListAccepted.

Lemma decodeItemSailRejectFromPrompt args :
  decodeItemC1BDomain args ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_decode_item (decodeItemSailCursor args))
    (decodeItemInstalledState (decodeItemInputBytes args)) true =
    (Reject RlpDecode, decodeItemInstalledState (decodeItemInputBytes args)) ->
  runRlpDecodeItem (decodeItemInputBytes args) (decodeItemSailCursor args) = Reject RlpDecode.
Proof.
  intros Hdomain Hrun. unfold runRlpDecodeItem, SailRun.runDecoder.
  rewrite (decodeItemSailInputSliceValid args Hdomain).
  unfold SailStdpp.Prompt_monad.bind0.
  erewrite decodeItemRunPromptBindSuccess with (value := tt)
    (rs' := decodeItemInstalledState (decodeItemInputBytes args));
    last apply decodeItemRunPromptInitialized.
  rewrite Hrun. reflexivity.
Qed.

Lemma decodeItemShortStringRejected args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  129 <= bv_unsigned prefix <= 183 ->
  Z.of_nat (List.length (decodeItemInputBytes args)) < 1 + (bv_unsigned prefix - 128) ->
  decodeItemRejectedFacts args.
Proof.
  intros Hdomain Hinput Hclass Hreject. split.
  - eapply decodeItemShortStringRejectedCandidateIntro; eauto.
    rewrite Z.mod_small; first exact Hreject. unfold word64Modulus. lia.
  - apply decodeItemSailRejectFromPrompt; first exact Hdomain.
    unfold decodeItemInputHead in Hinput. rewrite Hinput in Hreject.
    unfold decodeItemSailCursor. rewrite Hinput.
    eapply decodeItemRunPromptRejectedHeader; last exact Hreject.
    apply decodeItemRunPromptShortStringHeader; try reflexivity;
      auto using decodeItemInstalledBytes; lia.
Qed.

Lemma decodeItemShortListRejected args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  192 <= bv_unsigned prefix <= 247 ->
  Z.of_nat (List.length (decodeItemInputBytes args)) < 1 + (bv_unsigned prefix - 192) ->
  decodeItemRejectedFacts args.
Proof.
  intros Hdomain Hinput Hclass Hreject. split.
  - eapply decodeItemShortListRejectedCandidateIntro; eauto.
    rewrite Z.mod_small; first exact Hreject. unfold word64Modulus. lia.
  - apply decodeItemSailRejectFromPrompt; first exact Hdomain.
    unfold decodeItemInputHead in Hinput. rewrite Hinput in Hreject.
    unfold decodeItemSailCursor. rewrite Hinput.
    eapply decodeItemRunPromptRejectedHeader; last exact Hreject.
    apply decodeItemRunPromptShortListHeader; try reflexivity;
      auto using decodeItemInstalledBytes; lia.
Qed.

Print Assumptions decodeItemSailRejectFromPrompt.
Print Assumptions decodeItemShortStringRejected.
Print Assumptions decodeItemShortListRejected.

Lemma decodeItemLongCandidateFromProvenance args isList prefix rest n payloadStart lengthBytes :
  decodeItemFoldProvenance args isList prefix rest n payloadStart lengthBytes ->
  1 + n <= Z.of_nat (List.length (decodeItemInputBytes args)) ->
  (1 + n + bigEndian lengthBytes) mod word64Modulus <=
    Z.of_nat (List.length (decodeItemInputBytes args)) ->
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess isList (1 + n) (bigEndian lengthBytes).
Proof.
  intros (Hinput & Hclass & Hn & Hstart & Hbytes) Hheader Hfits.
  subst n. subst lengthBytes. destruct isList.
  - eapply decodeItemLongListCandidateIntro; eauto.
  - eapply decodeItemLongStringCandidateIntro; eauto.
Qed.

Lemma decodeItemLongAccepted args isList prefix rest n payloadStart lengthBytes :
  decodeItemC1BDomain args ->
  decodeItemFoldProvenance args isList prefix rest n payloadStart lengthBytes ->
  1 + n <= Z.of_nat (List.length (decodeItemInputBytes args)) ->
  (1 + n + bigEndian lengthBytes) mod word64Modulus <=
    Z.of_nat (List.length (decodeItemInputBytes args)) ->
  decodeItemLongAcceptedFacts args isList (1 + n) (bigEndian lengthBytes).
Proof.
  intros Hdomain Hprovenance Hheader Hfits.
  pose proof Hprovenance as HprovenanceSaved.
  assert (Hwidth : 1 <= n <= 8).
  { destruct Hprovenance as (_ & Hclass & Hn & _).
    destruct isList; simpl in Hclass; simpl in Hn; lia. }
  pose proof (decodeItemBigEndianNonnegative lengthBytes) as Hpayload.
  pose proof (decodeItemRunPromptLongHeader args isList prefix rest n payloadStart
    lengthBytes Hprovenance Hheader) as Hrun.
  destruct Hprovenance as (Hinput & Hclass & Hn & Hstart & Hbytes).
  split.
  - exact (decodeItemLongCandidateFromProvenance args isList prefix rest n payloadStart
      lengthBytes HprovenanceSaved Hheader Hfits).
  - destruct (Z_lt_ge_dec (1 + n + bigEndian lengthBytes) word64Modulus) as [Hnormal|Hwrap].
    + left. split; first exact Hnormal.
      rewrite Z.mod_small in Hfits; last lia.
      apply decodeItemSailSuccessFromPrompt; first exact Hdomain.
      unfold decodeItemInputHead in Hinput.
      unfold decodeItemSailCursor in Hrun. rewrite Hinput in Hrun.
      unfold decodeItemSailCursor. rewrite Hinput. rewrite Hinput in Hfits.
      eapply decodeItemRunPromptAcceptedHeader; try reflexivity; try exact Hrun;
        try exact Hfits; lia.
    + right. split.
      * unfold binaryWrapCase. repeat split; try reflexivity; lia.
      * apply decodeItemSailRejectFromPrompt; first exact Hdomain.
        pose proof (decodeItemSailInputLengthBound args Hdomain) as Hbound.
        unfold stateless_input_region_bound in Hbound.
        unfold decodeItemInputHead in Hinput.
        unfold decodeItemSailCursor in Hrun. rewrite Hinput in Hrun.
        unfold decodeItemSailCursor. rewrite Hinput. rewrite Hinput in Hbound.
        eapply decodeItemRunPromptRejectedHeader; first exact Hrun.
        unfold word64Modulus in Hwrap.
        assert (Hsizes : 2 ^ 32 - 1 < 2 ^ 64) by (vm_compute; reflexivity).
        apply Z.ge_le in Hwrap.
        eapply Z.lt_le_trans; last exact Hwrap.
        eapply Z.le_lt_trans; eauto.
Qed.

Lemma decodeItemLongStringAccepted args prefix rest n payloadStart lengthBytes :
  decodeItemC1BDomain args ->
  decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes ->
  1 + n <= Z.of_nat (List.length (decodeItemInputBytes args)) ->
  (1 + n + bigEndian lengthBytes) mod word64Modulus <=
    Z.of_nat (List.length (decodeItemInputBytes args)) ->
  decodeItemLongAcceptedFacts args false (1 + n) (bigEndian lengthBytes).
Proof. exact (decodeItemLongAccepted args false prefix rest n payloadStart lengthBytes). Qed.

Lemma decodeItemLongListAccepted args prefix rest n payloadStart lengthBytes :
  decodeItemC1BDomain args ->
  decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes ->
  1 + n <= Z.of_nat (List.length (decodeItemInputBytes args)) ->
  (1 + n + bigEndian lengthBytes) mod word64Modulus <=
    Z.of_nat (List.length (decodeItemInputBytes args)) ->
  decodeItemLongAcceptedFacts args true (1 + n) (bigEndian lengthBytes).
Proof. exact (decodeItemLongAccepted args true prefix rest n payloadStart lengthBytes). Qed.

Print Assumptions decodeItemLongCandidateFromProvenance.
Print Assumptions decodeItemLongAccepted.
Print Assumptions decodeItemLongStringAccepted.
Print Assumptions decodeItemLongListAccepted.

Lemma decodeItemLongStringHeaderRejected args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  184 <= bv_unsigned prefix <= 191 ->
  Z.of_nat (List.length (decodeItemInputBytes args)) < 1 + (bv_unsigned prefix - 183) ->
  decodeItemRejectedFacts args.
Proof.
  intros Hdomain Hinput Hclass Hreject. split.
  - eapply decodeItemLongStringHeaderRejectedCandidateIntro; eauto.
  - apply decodeItemSailRejectFromPrompt; first exact Hdomain.
    unfold decodeItemInputHead in Hinput. rewrite Hinput in Hreject.
    unfold decodeItemSailCursor. rewrite Hinput.
    apply decodeItemRunPromptHeaderReject.
    apply decodeItemRunPromptLongStringHeaderRejected; try reflexivity;
      auto using decodeItemInstalledBytes.
Qed.

Print Assumptions decodeItemLongStringHeaderRejected.

Lemma decodeItemLongListHeaderRejected args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  248 <= bv_unsigned prefix <= 255 ->
  Z.of_nat (List.length (decodeItemInputBytes args)) < 1 + (bv_unsigned prefix - 247) ->
  decodeItemRejectedFacts args.
Proof.
  intros Hdomain Hinput Hclass Hreject. split.
  - eapply decodeItemLongListHeaderRejectedCandidateIntro; eauto.
  - apply decodeItemSailRejectFromPrompt; first exact Hdomain.
    unfold decodeItemInputHead in Hinput. rewrite Hinput in Hreject.
    unfold decodeItemSailCursor. rewrite Hinput.
    apply decodeItemRunPromptHeaderReject.
    apply decodeItemRunPromptLongListHeaderRejected; try reflexivity;
      auto using decodeItemInstalledBytes.
Qed.

Print Assumptions decodeItemLongListHeaderRejected.

Lemma decodeItemLongPayloadRejected args isList prefix rest n payloadStart lengthBytes :
  decodeItemC1BDomain args ->
  decodeItemFoldProvenance args isList prefix rest n payloadStart lengthBytes ->
  1 + n <= Z.of_nat (List.length (decodeItemInputBytes args)) ->
  Z.of_nat (List.length (decodeItemInputBytes args)) <
    (1 + n + bigEndian lengthBytes) mod word64Modulus ->
  decodeItemRejectedFacts args.
Proof.
  intros Hdomain Hprovenance Hheader Hreject.
  pose proof (decodeItemRunPromptLongHeader args isList prefix rest n payloadStart
    lengthBytes Hprovenance Hheader) as Hrun.
  pose proof (decodeItemBigEndianNonnegative lengthBytes) as Hpayload.
  assert (Hwidth : 1 <= n <= 8).
  { destruct Hprovenance as (_ & Hclass & Hn & _).
    destruct isList; simpl in Hclass; simpl in Hn; lia. }
  destruct Hprovenance as (Hinput & Hclass & Hn & Hstart & Hbytes).
  split.
  - subst n. subst lengthBytes. destruct isList.
    + eapply decodeItemLongListPayloadRejectedCandidateIntro; eauto.
    + eapply decodeItemLongStringPayloadRejectedCandidateIntro; eauto.
  - apply decodeItemSailRejectFromPrompt; first exact Hdomain.
    assert (Hsum : (1 + n + bigEndian lengthBytes) mod word64Modulus <=
      1 + n + bigEndian lengthBytes).
    { apply Z.mod_le; first lia. unfold word64Modulus. lia. }
    unfold decodeItemInputHead in Hinput.
    unfold decodeItemSailCursor in Hrun. rewrite Hinput in Hrun.
    unfold decodeItemSailCursor. rewrite Hinput. rewrite Hinput in Hreject.
    eapply decodeItemRunPromptRejectedHeader; first exact Hrun.
    eapply Z.lt_le_trans; eauto.
Qed.

Lemma decodeItemLongStringPayloadRejected args prefix rest n payloadStart lengthBytes :
  decodeItemC1BDomain args ->
  decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes ->
  1 + n <= Z.of_nat (List.length (decodeItemInputBytes args)) ->
  Z.of_nat (List.length (decodeItemInputBytes args)) <
    (1 + n + bigEndian lengthBytes) mod word64Modulus ->
  decodeItemRejectedFacts args.
Proof. exact (decodeItemLongPayloadRejected args false prefix rest n payloadStart lengthBytes). Qed.

Lemma decodeItemLongListPayloadRejected args prefix rest n payloadStart lengthBytes :
  decodeItemC1BDomain args ->
  decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes ->
  1 + n <= Z.of_nat (List.length (decodeItemInputBytes args)) ->
  Z.of_nat (List.length (decodeItemInputBytes args)) <
    (1 + n + bigEndian lengthBytes) mod word64Modulus ->
  decodeItemRejectedFacts args.
Proof. exact (decodeItemLongPayloadRejected args true prefix rest n payloadStart lengthBytes). Qed.

Print Assumptions decodeItemLongPayloadRejected.
Print Assumptions decodeItemLongStringPayloadRejected.
Print Assumptions decodeItemLongListPayloadRejected.
