Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Require Import ZesuSsz.Compliance.DecodeItemReturnExitResources.
From Coq Require Import ZArith Lia.
Open Scope Z_scope.

Local Ltac decodeItemReturnMeaning openEntry meaning :=
  let Hcore := ident:(Hcore) in let Hfacts := ident:(Hfacts) in
  openEntry; unfold decodeItemReturnEntryCore;
  iIntros "(Hcore & %Hfacts)";
  iDestruct "Hcore" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hcore & _)";
  iPureIntro; pose proof (proj2 (proj1 Hcore));
  intros; repeat match goal with H : _ /\ _ |- _ => destruct H end;
  eapply meaning; eauto; unfold word64Modulus; lia.

Lemma decodeItemReturn698cLiteralMeaning `{!islaG Sigma} `{!threadG}
    args (x11 x12 x13 x14 x15 x16 : bv 64)
    (outputBytes frameBytes : list byte)
    (inputPrefix : byte) (rest : list byte) :
  decodeItemEntryAt800d698cLiteral args x11 x12 x13 x14 x15 x16
    outputBytes frameBytes inputPrefix rest ⊢
  ⌜(forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess false 0 1) ->
    DecodeMeaningModuloKnownBugs args after)%Z⌝.
Proof. decodeItemReturnMeaning ltac:(unfold decodeItemEntryAt800d698cLiteral) decodeItemLiteralPostMeaning. Qed.

Print Assumptions decodeItemReturn698cLiteralMeaning.

Lemma decodeItemReturn698cShortStringMeaning `{!islaG Sigma} `{!threadG}
    args (x11 x12 x13 x14 x15 x16 : bv 64)
    (outputBytes frameBytes : list byte)
    (inputPrefix : byte) (rest : list byte) :
  decodeItemEntryAt800d698cShortString args x11 x12 x13 x14 x15 x16
    outputBytes frameBytes inputPrefix rest ⊢
  ⌜(forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess false 1 (bv_unsigned inputPrefix - 128)) ->
    DecodeMeaningModuloKnownBugs args after)%Z⌝.
Proof. decodeItemReturnMeaning ltac:(unfold decodeItemEntryAt800d698cShortString) decodeItemShortStringPostMeaning. Qed.

Print Assumptions decodeItemReturn698cShortStringMeaning.

Lemma decodeItemReturn69b0Meaning `{!islaG Sigma} `{!threadG}
    args locals prefix rest :
  decodeItemEntryAt800d69b0 args locals prefix rest ⊢
  ⌜(forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess false 1 0) ->
    DecodeMeaningModuloKnownBugs args after)%Z⌝.
Proof. decodeItemReturnMeaning ltac:(unfold decodeItemEntryAt800d69b0) decodeItemEmptyStringPostMeaning. Qed.

Print Assumptions decodeItemReturn69b0Meaning.

Lemma decodeItemReturn6a40Meaning `{!islaG Sigma} `{!threadG}
    args locals prefix rest headerLength payloadLength :
  decodeItemEntryAt800d6a40 args locals prefix rest headerLength payloadLength ⊢
  ⌜(forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess false headerLength payloadLength) ->
    DecodeMeaningModuloKnownBugs args after)%Z⌝.
Proof. decodeItemReturnMeaning ltac:(unfold decodeItemEntryAt800d6a40) decodeItemLongStringPostMeaning. Qed.

Print Assumptions decodeItemReturn6a40Meaning.

Lemma decodeItemReturn6a78Meaning `{!islaG Sigma} `{!threadG}
    args locals prefix rest :
  decodeItemEntryAt800d6a78 args locals prefix rest ⊢
  ⌜(forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess true 1 (bv_unsigned prefix - 192)) ->
    DecodeMeaningModuloKnownBugs args after)%Z⌝.
Proof. decodeItemReturnMeaning ltac:(unfold decodeItemEntryAt800d6a78) decodeItemShortListPostMeaning. Qed.

Print Assumptions decodeItemReturn6a78Meaning.

Lemma decodeItemReturn6ae0Meaning `{!islaG Sigma} `{!threadG}
    args locals  :
  decodeItemEntryAt800d6ae0 args locals ⊢
  ⌜(forall after, errorResult40 after ->
    encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateError) ->
    DecodeMeaningModuloKnownBugs args after)%Z⌝.
Proof. decodeItemReturnMeaning ltac:(unfold decodeItemEntryAt800d6ae0) decodeItemErrorPostMeaning. Qed.

Print Assumptions decodeItemReturn6ae0Meaning.

Lemma decodeItemReturn6b08Meaning `{!islaG Sigma} `{!threadG}
    args locals prefix rest headerLength payloadLength :
  decodeItemEntryAt800d6b08 args locals prefix rest headerLength payloadLength ⊢
  ⌜(forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess true headerLength payloadLength) ->
    DecodeMeaningModuloKnownBugs args after)%Z⌝.
Proof. decodeItemReturnMeaning ltac:(unfold decodeItemEntryAt800d6b08) decodeItemLongListPostMeaning. Qed.

Print Assumptions decodeItemReturn6b08Meaning.

