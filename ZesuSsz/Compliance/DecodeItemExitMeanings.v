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

Lemma decodeItemReturn698cMeaning `{!islaG Sigma} `{!threadG}
    args locals pointerBytes lengthBytes prefix rest isLiteral :
  decodeItemEntryAt800d698c args locals pointerBytes lengthBytes prefix rest isLiteral ⊢
  ⌜(forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess false (if isLiteral then 0 else 1) (if isLiteral then 1 else bv_unsigned prefix - 128)) ->
    DecodeMeaningModuloKnownBugs args after)%Z⌝.
Proof.
  unfold decodeItemEntryAt800d698c, decodeItemReturnEntryCore.
  iIntros "(Hcore & %Hfacts)".
  iDestruct "Hcore" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hcore & _)".
  iPureIntro.
  intros after Himage.
  destruct Hfacts as (Hhead & Hprefix & Hpointer & Hlength & Hconsumed & Haccepted & _).
  destruct isLiteral; simpl in *.
  { exact (decodeItemLiteralPostMeaning args after (proj2 (proj1 Hcore)) Haccepted Himage). }
  { eapply (decodeItemShortStringPostMeaning args after (bv_unsigned prefix - 128));
      try eassumption; try exact (proj2 (proj1 Hcore)); unfold word64Modulus; lia. }
Qed.

Print Assumptions decodeItemReturn698cMeaning.

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

