Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Compliance.DecodeItemReturnExitResources.
Open Scope Z_scope.

Lemma decodeItemReturnAt69b0Image args after :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemAcceptedFacts args false 1 0 ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after (candidateSuccess false 1 0) ->
  after = decodeItemOkBytes (decodeItemBeforeStorage args)
    (word64Bytes 1) (word64Bytes 0) (word64Bytes 1) false ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
  DecodeMeaningModuloKnownBugs args
    (decodeItemOkBytes (decodeItemBeforeStorage args)
      (word64Bytes 1) (word64Bytes 0) (word64Bytes 1) false).
Proof.
  intros Hdomain Haccepted Himage ->. split; [exact Hdomain |].
  eapply decodeItemEmptyStringPostMeaning; [exact (proj2 Hdomain) | exact Haccepted | exact Himage].
Qed.

Lemma decodeItemReturnAt6a78Image args locals (inputPrefix : byte) after :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  192 <= bv_unsigned inputPrefix <= 247 ->
  bv_unsigned (returnA3 locals) = bv_unsigned inputPrefix - 192 ->
  decodeItemAcceptedFacts args true 1 (bv_unsigned inputPrefix - 192) ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after
    (candidateSuccess true 1 (bv_unsigned inputPrefix - 192)) ->
  after = decodeItemOkBytes (decodeItemBeforeStorage args)
    (word64Bytes (bv_unsigned (returnA1 locals) + 1))
    (word64Bytes (bv_unsigned (returnA3 locals)))
    (word64Bytes (bv_unsigned (returnA3 locals) + 1)) true ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
  DecodeMeaningModuloKnownBugs args
    (decodeItemOkBytes (decodeItemBeforeStorage args)
      (word64Bytes (bv_unsigned (returnA1 locals) + 1))
      (word64Bytes (bv_unsigned (returnA3 locals)))
      (word64Bytes (bv_unsigned (returnA3 locals) + 1)) true).
Proof.
  intros Hdomain Hclass Hlength Haccepted Himage ->. split; [exact Hdomain |].
  eapply decodeItemShortListPostMeaning;
    [exact (proj2 Hdomain) | exact Haccepted | exact Himage | lia |].
  unfold word64Modulus. lia.
Qed.

Lemma decodeItemReturnAt6ae0Image args after :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemRejectedFacts args ->
  errorResult40 after ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after candidateError ->
  after = errorEncoding ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
  DecodeMeaningModuloKnownBugs args errorEncoding.
Proof.
  intros Hdomain Hrejected Herror Himage ->. split; [exact Hdomain |].
  eapply decodeItemErrorPostMeaning; [exact (proj2 Hdomain) | exact Hrejected | exact Herror | exact Himage].
Qed.

Print Assumptions decodeItemReturnAt69b0Image.
Print Assumptions decodeItemReturnAt6a78Image.
Print Assumptions decodeItemReturnAt6ae0Image.
