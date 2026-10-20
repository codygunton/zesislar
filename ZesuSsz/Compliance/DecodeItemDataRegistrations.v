Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
From Coq Require Import List ZArith.
Open Scope Z_scope.
Require Import ZesuSsz.Compliance.DecodeItemEntryIntroductions.
Require Import ZesuSsz.Compliance.DecodeItemLoopSteps.

Require Import ZesuSsz.Automation.EntryIntro.

Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Require Import ZesuSsz.Compliance.DecodeItemReturnExitResources.
From Coq Require Import ZArith Lia.
Require Import ZesuSsz.Compliance.DecodeItemExitMeanings.
Require Import ZesuSsz.Automation.ReturnRoute.

#[export] Instance decodeItemEntry6a08IntroductionRegistered `{!islaG Sigma} `{!threadG}
    args frameBytes (x13 : bv 64) prefix rest :
  ZesuEntryIntro (decodeItemEntryAt800d6a08 args frameBytes x13 prefix rest) _ :=
  decodeItemEntry6a08Introduction args frameBytes x13 prefix rest.

#[export] Instance decodeItemEntry6aa8IntroductionRegistered `{!islaG Sigma} `{!threadG}
    args frameBytes (x13 : bv 64) prefix rest :
  ZesuEntryIntro (decodeItemEntryAt800d6aa8 args frameBytes x13 prefix rest) _ :=
  decodeItemEntry6aa8Introduction args frameBytes x13 prefix rest.

#[export] Instance decodeItemEntry6a38IntroductionRegistered `{!islaG Sigma} `{!threadG}
    args n payloadStart lengthBytes frameBytes (loaded : bv 64) prefix rest :
  ZesuEntryIntro (decodeItemEntryAt800d6a38 args n payloadStart lengthBytes frameBytes loaded prefix rest) _ :=
  decodeItemEntry6a38Introduction args n payloadStart lengthBytes frameBytes loaded prefix rest.

#[export] Instance decodeItemEntry6ad8IntroductionRegistered `{!islaG Sigma} `{!threadG}
    args n payloadStart lengthBytes frameBytes (loaded : bv 64) prefix rest :
  ZesuEntryIntro (decodeItemEntryAt800d6ad8 args n payloadStart lengthBytes frameBytes loaded prefix rest) _ :=
  decodeItemEntry6ad8Introduction args n payloadStart lengthBytes frameBytes loaded prefix rest.

#[export] Instance decodeItemHeader6a24StepRegistered `{!islaG Sigma} `{!threadG}
    args n i payloadStart lengthBytes frameBytes (loaded : bv 64) :
  ZesuLoopStep
    (decodeItemByteFoldStringHeader args n i payloadStart lengthBytes frameBytes loaded)
    ((forall next : byte, i < n ->
    nth_error lengthBytes (Z.to_nat i) = Some next ->
    decodeItemByteFoldFacts args n (i + 1) payloadStart lengthBytes /\
    bigEndian (firstn (Z.to_nat (i + 1)) lengthBytes) =
      256 * bigEndian (firstn (Z.to_nat i) lengthBytes) + bv_unsigned next)%Z) :=
  decodeItemHeader6a24Step args n i payloadStart lengthBytes frameBytes loaded.

#[export] Instance decodeItemHeader6ac4StepRegistered `{!islaG Sigma} `{!threadG}
    args n i payloadStart lengthBytes frameBytes (loaded : bv 64) :
  ZesuLoopStep
    (decodeItemByteFoldListHeader args n i payloadStart lengthBytes frameBytes loaded)
    ((forall next : byte, i < n ->
    nth_error lengthBytes (Z.to_nat i) = Some next ->
    decodeItemByteFoldFacts args n (i + 1) payloadStart lengthBytes /\
    bigEndian (firstn (Z.to_nat (i + 1)) lengthBytes) =
      256 * bigEndian (firstn (Z.to_nat i) lengthBytes) + bv_unsigned next)%Z) :=
  decodeItemHeader6ac4Step args n i payloadStart lengthBytes frameBytes loaded.

(* Reviewed E3-integrated R3 registrations. Original class commit: 7d7a2ffc7bfe9d9cf43683f616d83b326dd74e7b.
   This scope registers five unchanged sources and two public 698c alternatives. *)
Lemma decodeItemExitMeaning698cLiteralDraft `{!islaG Sigma} `{!threadG}
    args (x11 x12 x13 x14 x15 x16 : bv 64)
    (outputBytes frameBytes : list byte)
    (inputPrefix : byte) (rest : list byte) :
  ZesuExitMeaning (decodeItemEntryAt800d698cLiteral args x11 x12 x13 x14 x15 x16
    outputBytes frameBytes inputPrefix rest) ((forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess false 0 1) ->
    DecodeMeaningModuloKnownBugs args after)%Z).
Proof. constructor. apply decodeItemReturn698cLiteralMeaning. Qed.
#[export] Existing Instance decodeItemExitMeaning698cLiteralDraft.

Lemma decodeItemExitMeaning698cShortStringDraft `{!islaG Sigma} `{!threadG}
    args (x11 x12 x13 x14 x15 x16 : bv 64)
    (outputBytes frameBytes : list byte)
    (inputPrefix : byte) (rest : list byte) :
  ZesuExitMeaning (decodeItemEntryAt800d698cShortString args x11 x12 x13 x14 x15 x16
    outputBytes frameBytes inputPrefix rest) ((forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess false 1 (bv_unsigned inputPrefix - 128)) ->
    DecodeMeaningModuloKnownBugs args after)%Z).
Proof. constructor. apply decodeItemReturn698cShortStringMeaning. Qed.
#[export] Existing Instance decodeItemExitMeaning698cShortStringDraft.


Lemma decodeItemExitMeaning69b0Draft `{!islaG Sigma} `{!threadG}
    args locals prefix rest :
  ZesuExitMeaning (decodeItemEntryAt800d69b0 args locals prefix rest) ((forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess false 1 0) ->
    DecodeMeaningModuloKnownBugs args after)%Z).
Proof. constructor. apply decodeItemReturn69b0Meaning. Qed.
#[export] Existing Instance decodeItemExitMeaning69b0Draft.

Lemma decodeItemExitMeaning6a40Draft `{!islaG Sigma} `{!threadG}
    args locals prefix rest headerLength payloadLength :
  ZesuExitMeaning (decodeItemEntryAt800d6a40 args locals prefix rest headerLength payloadLength) ((forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess false headerLength payloadLength) ->
    DecodeMeaningModuloKnownBugs args after)%Z).
Proof. constructor. apply decodeItemReturn6a40Meaning. Qed.
#[export] Existing Instance decodeItemExitMeaning6a40Draft.

Lemma decodeItemExitMeaning6a78Draft `{!islaG Sigma} `{!threadG}
    args locals prefix rest :
  ZesuExitMeaning (decodeItemEntryAt800d6a78 args locals prefix rest) ((forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess true 1 (bv_unsigned prefix - 192)) ->
    DecodeMeaningModuloKnownBugs args after)%Z).
Proof. constructor. apply decodeItemReturn6a78Meaning. Qed.
#[export] Existing Instance decodeItemExitMeaning6a78Draft.

Lemma decodeItemExitMeaning6ae0Draft `{!islaG Sigma} `{!threadG}
    args locals  :
  ZesuExitMeaning (decodeItemEntryAt800d6ae0 args locals) ((forall after, errorResult40 after ->
    encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateError) ->
    DecodeMeaningModuloKnownBugs args after)%Z).
Proof. constructor. apply decodeItemReturn6ae0Meaning. Qed.
#[export] Existing Instance decodeItemExitMeaning6ae0Draft.

Lemma decodeItemExitMeaning6b08Draft `{!islaG Sigma} `{!threadG}
    args locals prefix rest headerLength payloadLength :
  ZesuExitMeaning (decodeItemEntryAt800d6b08 args locals prefix rest headerLength payloadLength) ((forall after, encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
      (decodeItemBeforeStorage args) after (candidateSuccess true headerLength payloadLength) ->
    DecodeMeaningModuloKnownBugs args after)%Z).
Proof. constructor. apply decodeItemReturn6b08Meaning. Qed.
#[export] Existing Instance decodeItemExitMeaning6b08Draft.

