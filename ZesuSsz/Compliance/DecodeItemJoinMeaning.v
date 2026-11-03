Require Import ZesuSsz.Automation.All.
From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions list_numbers list.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Automation.AdditiveDecoder.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Automation.JoinEntailment.
Require Import ZesuSsz.Compliance.DecodeItemSailIntroduction.
Require Import ZesuSsz.Compliance.DecodeItemReturnExitResources.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Open Scope Z_scope.

Lemma decodeItemJoinWordCodec (word : bv 64) :
  littleEndian (bv_to_little_endian 8 8 (bv_unsigned word)) = bv_unsigned word.
Proof.
  change (zesu_additive_decoder 8 (bv_to_little_endian 8 8 (bv_unsigned word)) = bv_unsigned word).
  apply JoinEntailment.zesu_join_word_codec; lia.
Qed.

Lemma decodeItemJoinLiteralMeaning args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  bv_unsigned prefix <= 127 ->
  DecodeMeaningModuloKnownBugs args
    (decodeItemOkBytes (decodeItemBeforeStorage args)
      (bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args))))
      (bv_to_little_endian 8 8 (bv_unsigned (BV 64 1)))
      (bv_to_little_endian 8 8 (bv_unsigned (BV 64 1))) false).
Proof.
  intros Hwf Hhead Hprefix.
  pose proof Hwf as Hlayout.
  unfold decodeItemC1BDomain, decodeItemArgsWellFormed in Hlayout.
  destruct Hlayout as [HinputLength [HbeforeLength Hlayout]].
  eapply decodeItemLiteralPostMeaning; [exact Hwf | |].
  - eapply decodeItemLiteralAccepted; eassumption.
  - eapply decodeItemOkBytes_encodeSuccess.
    all: try exact HbeforeLength.
    all: try (rewrite (length_bv_to_little_endian 8 8 _ ltac:(lia)); reflexivity).
    all: rewrite decodeItemJoinWordCodec.
    all: try reflexivity.
    assert (Hcast : bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args)) = decodeItemInputPointer args).
    { clear - Hlayout. Hooks.zesu_stack_arithmetic. }
    rewrite Hcast.
    assert (Hnot128 : (bv_unsigned prefix =? 128) = false).
    { apply Z.eqb_neq. lia. }
    unfold decodeItemInputHead in Hhead.
    unfold itemPayloadPointer. rewrite Hhead.
    rewrite Hnot128. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma decodeItemJoinShortMeaning args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  129 <= bv_unsigned prefix <= 183 ->
  1 + (bv_unsigned prefix - 128) <= Z.of_nat (List.length (decodeItemInputBytes args)) ->
  DecodeMeaningModuloKnownBugs args
    (decodeItemOkBytes (decodeItemBeforeStorage args)
      (bv_to_little_endian 8 8 (bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (BV 64 1))))
      (bv_to_little_endian 8 8 (bv_unsigned (bv_and (bv_and (bv_sign_extend 64 prefix) (BV 64 255)) (BV 64 127))))
      (bv_to_little_endian 8 8 (bv_unsigned (bv_add (bv_and (bv_and (bv_sign_extend 64 prefix) (BV 64 255)) (BV 64 127)) (BV 64 1)))) false).
Proof.
  intros Hwf Hhead Hprefix Hcount.
  set (payload := bv_and (bv_and (bv_sign_extend 64 prefix) (BV 64 255)) (BV 64 127)) in *.
  pose proof (JoinEntailment.zesu_join_mask_payload prefix
    (Z.le_trans 128 129 _ ltac:(vm_compute; congruence) (proj1 Hprefix))) as Hpayload.
  change (bv_unsigned payload = bv_unsigned prefix - 128) in Hpayload.
  pose proof Hwf as Hlayout.
  unfold decodeItemC1BDomain, decodeItemArgsWellFormed in Hlayout.
  destruct Hlayout as [HinputLength [HbeforeLength Hlayout]].
  assert (Hpositive : 1 <= decodeItemInputLength args).
  { clear - Hcount Hprefix HinputLength. lia. }
  assert (Hcast : bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (BV 64 1)) = decodeItemInputPointer args + 1).
  { clear - Hlayout Hpositive. unfold decodeItemEntryLayout in Hlayout. Hooks.zesu_stack_arithmetic. }
  assert (Hconsumed : bv_unsigned (bv_add payload (BV 64 1)) = 1 + (bv_unsigned prefix - 128)).
  { rewrite bv_add_unsigned. rewrite Hpayload. rewrite bv_unsigned_BV.
    assert (Hsmall : 0 <= bv_unsigned prefix - 128 + 1 < bv_modulus 64).
    { change (0 <= bv_unsigned prefix - 128 + 1 < 18446744073709551616). lia. }
    rewrite (bv_wrap_small 64 (bv_unsigned prefix - 128 + 1) Hsmall). lia. }
  eapply (decodeItemShortStringPostMeaning args _ (bv_unsigned prefix - 128)).
  - exact Hwf.
  - eapply decodeItemShortStringAccepted; eassumption.
  - eapply decodeItemOkBytes_encodeSuccess.
    all: try exact HbeforeLength.
    all: try (rewrite (length_bv_to_little_endian 8 8 _ ltac:(lia)); reflexivity).
    all: rewrite decodeItemJoinWordCodec.
    all: try (rewrite Hpayload; reflexivity).
    all: try (rewrite Hconsumed; symmetry; apply Z.mod_small; unfold word64Modulus; lia).
    rewrite Hcast.
    assert (Hnot128 : (bv_unsigned prefix =? 128) = false).
    { apply Z.eqb_neq. lia. }
    unfold decodeItemInputHead in Hhead.
    unfold itemPayloadPointer. rewrite Hhead.
    rewrite Hnot128. reflexivity.
  - lia.
  - unfold word64Modulus. lia.
Qed.
