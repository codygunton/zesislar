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

Lemma decodeItemReturn698cLiteralMeaning `{!islaG Sigma} `{!threadG}
    args (x11 x12 x13 x14 x15 x16 : bv 64)
    (outputBytes frameBytes pointerBytes lengthBytes : list byte)
    (inputPrefix : byte) (rest : list byte) :
  decodeItemEntryAt800d698cLiteral args x11 x12 x13 x14 x15 x16
    outputBytes frameBytes pointerBytes lengthBytes inputPrefix rest ⊢
  ⌜(forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess false 0 1) ->
    DecodeMeaningModuloKnownBugs args after)%Z⌝.
Proof.
  unfold decodeItemEntryAt800d698cLiteral, decodeItemReturnEntryCore.
  iIntros "(Hcore & %Hfacts)".
  iDestruct "Hcore" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hcore & _)".
  iPureIntro. intros after Himage.
  destruct Hfacts as (Hhead & Hprefix & Hpointer & Hlength & Hconsumed & Haccepted & _).
  exact (decodeItemLiteralPostMeaning args after (proj2 (proj1 Hcore)) Haccepted Himage).
Qed.

Print Assumptions decodeItemReturn698cLiteralMeaning.

Lemma decodeItemReturn698cShortStringMeaning `{!islaG Sigma} `{!threadG}
    args (x11 x12 x13 x14 x15 x16 : bv 64)
    (outputBytes frameBytes pointerBytes lengthBytes : list byte)
    (inputPrefix : byte) (rest : list byte) :
  decodeItemEntryAt800d698cShortString args x11 x12 x13 x14 x15 x16
    outputBytes frameBytes pointerBytes lengthBytes inputPrefix rest ⊢
  ⌜(forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess false 1 (bv_unsigned inputPrefix - 128)) ->
    DecodeMeaningModuloKnownBugs args after)%Z⌝.
Proof.
  unfold decodeItemEntryAt800d698cShortString, decodeItemReturnEntryCore.
  iIntros "(Hcore & %Hfacts)".
  iDestruct "Hcore" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hcore & _)".
  iPureIntro. intros after Himage.
  destruct Hfacts as (Hhead & Hprefix & Hpointer & Hlength & Hconsumed & Haccepted & _).
  eapply (decodeItemShortStringPostMeaning args after (bv_unsigned inputPrefix - 128));
    try eassumption; try exact (proj2 (proj1 Hcore)).
  { change (0 <= @bv_unsigned 8%N inputPrefix - 128)%Z; apply (proj2 (Z.le_0_sub 128 (@bv_unsigned 8%N inputPrefix))); eapply Z.le_trans with (m := 129%Z); [vm_compute; discriminate | exact (proj1 Hprefix)]. }
  { change (1 + (@bv_unsigned 8%N inputPrefix - 128) < 18446744073709551616)%Z; eapply Z.le_lt_trans with (m := (1 + (183 - 128))%Z); [apply (proj1 (Z.add_le_mono_l _ _ 1)); apply (proj1 (Z.sub_le_mono_r _ _ 128)); exact (proj2 Hprefix) | vm_compute; reflexivity]. }
Qed.

Print Assumptions decodeItemReturn698cShortStringMeaning.

Lemma decodeItemReturn69b0Meaning `{!islaG Sigma} `{!threadG}
    args locals prefix rest :
  decodeItemEntryAt800d69b0 args locals prefix rest ⊢
  ⌜(forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess false 1 0) ->
    DecodeMeaningModuloKnownBugs args after)%Z⌝.
Proof.
  unfold decodeItemEntryAt800d69b0, decodeItemReturnEntryCore.
  iIntros "(Hcore & %Hfacts)".
  iDestruct "Hcore" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hcore & _)".
  iPureIntro.
  intros after Himage. destruct Hfacts as (Hhead & Hprefix & Haccepted & _).
  exact (decodeItemEmptyStringPostMeaning args after (proj2 (proj1 Hcore)) Haccepted Himage).
Qed.

Print Assumptions decodeItemReturn69b0Meaning.

Lemma decodeItemReturn6a40Meaning `{!islaG Sigma} `{!threadG}
    args locals prefix rest headerLength payloadLength :
  decodeItemEntryAt800d6a40 args locals prefix rest headerLength payloadLength ⊢
  ⌜(forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess false headerLength payloadLength) ->
    DecodeMeaningModuloKnownBugs args after)%Z⌝.
Proof.
  unfold decodeItemEntryAt800d6a40, decodeItemReturnEntryCore.
  iIntros "(Hcore & %Hfacts)".
  iDestruct "Hcore" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hcore & _)".
  iPureIntro.
  intros after Himage.
  destruct Hfacts as (Hhead & Hprefix & Hheader & Hpayload & Hnonnegative &
    Hpointer & Hvalue & Hconsumed & Haccepted & _).
  eapply (decodeItemLongStringPostMeaning args after headerLength payloadLength);
    try eassumption; try exact (proj2 (proj1 Hcore)); lia.
Qed.

Print Assumptions decodeItemReturn6a40Meaning.

Lemma decodeItemReturn6a78Meaning `{!islaG Sigma} `{!threadG}
    args locals prefix rest :
  decodeItemEntryAt800d6a78 args locals prefix rest ⊢
  ⌜(forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess true 1 (bv_unsigned prefix - 192)) ->
    DecodeMeaningModuloKnownBugs args after)%Z⌝.
Proof.
  unfold decodeItemEntryAt800d6a78, decodeItemReturnEntryCore.
  iIntros "(Hcore & %Hfacts)".
  iDestruct "Hcore" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hcore & _)".
  iPureIntro.
  intros after Himage.
  destruct Hfacts as (Hhead & Hprefix & Hpointer & Hpayload & Haccepted & _).
  eapply (decodeItemShortListPostMeaning args after (bv_unsigned prefix - 192));
    try eassumption; try exact (proj2 (proj1 Hcore)); unfold word64Modulus; lia.
Qed.

Print Assumptions decodeItemReturn6a78Meaning.

Lemma decodeItemReturn6ae0Meaning `{!islaG Sigma} `{!threadG}
    args locals  :
  decodeItemEntryAt800d6ae0 args locals ⊢
  ⌜(forall after, errorResult40 after ->
    encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateError) ->
    DecodeMeaningModuloKnownBugs args after)%Z⌝.
Proof.
  unfold decodeItemEntryAt800d6ae0, decodeItemReturnEntryCore.
  iIntros "(Hcore & %Hfacts)".
  iDestruct "Hcore" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hcore & _)".
  iPureIntro.
  intros after Herror Himage. destruct Hfacts as [Hrejected Hstorage].
  exact (decodeItemErrorPostMeaning args after (proj2 (proj1 Hcore)) Hrejected Herror Himage).
Qed.

Print Assumptions decodeItemReturn6ae0Meaning.

Lemma decodeItemReturn6b08Meaning `{!islaG Sigma} `{!threadG}
    args locals prefix rest headerLength payloadLength :
  decodeItemEntryAt800d6b08 args locals prefix rest headerLength payloadLength ⊢
  ⌜(forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess true headerLength payloadLength) ->
    DecodeMeaningModuloKnownBugs args after)%Z⌝.
Proof.
  unfold decodeItemEntryAt800d6b08, decodeItemReturnEntryCore.
  iIntros "(Hcore & %Hfacts)".
  iDestruct "Hcore" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hcore & _)".
  iPureIntro.
  intros after Himage.
  destruct Hfacts as (Hhead & Hprefix & Hheader & Hpayload & Hnonnegative &
    Hpointer & Hvalue & Hconsumed & Haccepted & _).
  eapply (decodeItemLongListPostMeaning args after headerLength payloadLength);
    try eassumption; try exact (proj2 (proj1 Hcore)); lia.
Qed.

Print Assumptions decodeItemReturn6b08Meaning.

