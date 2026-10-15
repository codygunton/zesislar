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

Require Import ZesuSsz.Compliance.DecodeItemExitMeanings.

Require Import ZesuSsz.Automation.ReturnRoute.

(* UNEXPORTED E3-integrated R3 draft. Original class commit: 7d7a2ffc7bfe9d9cf43683f616d83b326dd74e7b.
   This scope registers five unchanged sources and two public 698c alternatives. *)
Lemma decodeItemExitMeaning698cLiteralDraft `{!islaG Sigma} `{!threadG}
    args (x11 x12 x13 x14 x15 x16 : bv 64)
    (outputBytes frameBytes pointerBytes lengthBytes : list byte)
    (inputPrefix : byte) (rest : list byte) :
  ZesuExitMeaning (decodeItemEntryAt800d698cLiteral args x11 x12 x13 x14 x15 x16
    outputBytes frameBytes pointerBytes lengthBytes inputPrefix rest) ((forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess false 0 1) ->
    DecodeMeaningModuloKnownBugs args after)%Z).
Proof. constructor. apply decodeItemReturn698cLiteralMeaning. Qed.
#[local] Existing Instance decodeItemExitMeaning698cLiteralDraft.

Lemma decodeItemExitMeaning698cShortStringDraft `{!islaG Sigma} `{!threadG}
    args (x11 x12 x13 x14 x15 x16 : bv 64)
    (outputBytes frameBytes pointerBytes lengthBytes : list byte)
    (inputPrefix : byte) (rest : list byte) :
  ZesuExitMeaning (decodeItemEntryAt800d698cShortString args x11 x12 x13 x14 x15 x16
    outputBytes frameBytes pointerBytes lengthBytes inputPrefix rest) ((forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess false 1 (bv_unsigned inputPrefix - 128)) ->
    DecodeMeaningModuloKnownBugs args after)%Z).
Proof. constructor. apply decodeItemReturn698cShortStringMeaning. Qed.
#[local] Existing Instance decodeItemExitMeaning698cShortStringDraft.


Lemma decodeItemExitMeaning69b0Draft `{!islaG Sigma} `{!threadG}
    args locals prefix rest :
  ZesuExitMeaning (decodeItemEntryAt800d69b0 args locals prefix rest) ((forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess false 1 0) ->
    DecodeMeaningModuloKnownBugs args after)%Z).
Proof. constructor. apply decodeItemReturn69b0Meaning. Qed.
#[local] Existing Instance decodeItemExitMeaning69b0Draft.

Lemma decodeItemExitMeaning6a40Draft `{!islaG Sigma} `{!threadG}
    args locals prefix rest headerLength payloadLength :
  ZesuExitMeaning (decodeItemEntryAt800d6a40 args locals prefix rest headerLength payloadLength) ((forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess false headerLength payloadLength) ->
    DecodeMeaningModuloKnownBugs args after)%Z).
Proof. constructor. apply decodeItemReturn6a40Meaning. Qed.
#[local] Existing Instance decodeItemExitMeaning6a40Draft.

Lemma decodeItemExitMeaning6a78Draft `{!islaG Sigma} `{!threadG}
    args locals prefix rest :
  ZesuExitMeaning (decodeItemEntryAt800d6a78 args locals prefix rest) ((forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess true 1 (bv_unsigned prefix - 192)) ->
    DecodeMeaningModuloKnownBugs args after)%Z).
Proof. constructor. apply decodeItemReturn6a78Meaning. Qed.
#[local] Existing Instance decodeItemExitMeaning6a78Draft.

Lemma decodeItemExitMeaning6ae0Draft `{!islaG Sigma} `{!threadG}
    args locals  :
  ZesuExitMeaning (decodeItemEntryAt800d6ae0 args locals) ((forall after, errorResult40 after ->
    encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateError) ->
    DecodeMeaningModuloKnownBugs args after)%Z).
Proof. constructor. apply decodeItemReturn6ae0Meaning. Qed.
#[local] Existing Instance decodeItemExitMeaning6ae0Draft.

Lemma decodeItemExitMeaning6b08Draft `{!islaG Sigma} `{!threadG}
    args locals prefix rest headerLength payloadLength :
  ZesuExitMeaning (decodeItemEntryAt800d6b08 args locals prefix rest headerLength payloadLength) ((forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess true headerLength payloadLength) ->
    DecodeMeaningModuloKnownBugs args after)%Z).
Proof. constructor. apply decodeItemReturn6b08Meaning. Qed.
#[local] Existing Instance decodeItemExitMeaning6b08Draft.

