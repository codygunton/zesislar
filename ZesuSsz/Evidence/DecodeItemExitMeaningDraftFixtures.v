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
Require Import ZesuSsz.Compliance.DecodeItemDataRegistrations.
#[local] Existing Instance decodeItemExitMeaning698cLiteralDraft.
Lemma r3FactsOutput698cLiteral `{!islaG Sigma} `{!threadG}
    args (x11 x12 x13 x14 x15 x16 : bv 64)
    (outputBytes frameBytes pointerBytes lengthBytes : list byte)
    (inputPrefix : byte) (rest : list byte) :
  exists facts : Prop, ZesuExitMeaning (decodeItemEntryAt800d698cLiteral args x11 x12 x13 x14 x15 x16
    outputBytes frameBytes pointerBytes lengthBytes inputPrefix rest) facts.
Proof. eexists. typeclasses eauto. Qed.

#[local] Existing Instance decodeItemExitMeaning698cShortStringDraft.
Lemma r3FactsOutput698cShortString `{!islaG Sigma} `{!threadG}
    args (x11 x12 x13 x14 x15 x16 : bv 64)
    (outputBytes frameBytes pointerBytes lengthBytes : list byte)
    (inputPrefix : byte) (rest : list byte) :
  exists facts : Prop, ZesuExitMeaning (decodeItemEntryAt800d698cShortString args x11 x12 x13 x14 x15 x16
    outputBytes frameBytes pointerBytes lengthBytes inputPrefix rest) facts.
Proof. eexists. typeclasses eauto. Qed.

