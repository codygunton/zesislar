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
Require Import ZesuSsz.Compliance.DecodeItemEntryAdditionalFacts.
Require Import ZesuSsz.Compliance.DecodeItemLoopSteps.

Require Import ZesuSsz.Automation.EntryIntro.

#[export] Instance decodeItemEntry6a08IntroductionRegistered `{!islaG Sigma} `{!threadG}
    args frameBytes (x13 : bv 64) prefix rest :
  ZesuEntryIntro (decodeItemEntryAt800d6a08 args frameBytes x13 prefix rest) _ :=
  decodeItemEntry6a08AdditionalIntroduction args frameBytes x13 prefix rest.

#[export] Instance decodeItemEntry6aa8IntroductionRegistered `{!islaG Sigma} `{!threadG}
    args frameBytes (x13 : bv 64) prefix rest :
  ZesuEntryIntro (decodeItemEntryAt800d6aa8 args frameBytes x13 prefix rest) _ :=
  decodeItemEntry6aa8AdditionalIntroduction args frameBytes x13 prefix rest.

#[export] Instance decodeItemEntry6a38IntroductionRegistered `{!islaG Sigma} `{!threadG}
    args n payloadStart lengthBytes frameBytes (loaded : bv 64) prefix rest :
  ZesuEntryIntro (decodeItemEntryAt800d6a38 args n payloadStart lengthBytes frameBytes loaded prefix rest) _ :=
  decodeItemEntry6a38AdditionalIntroduction args n payloadStart lengthBytes frameBytes loaded prefix rest.

#[export] Instance decodeItemEntry6ad8IntroductionRegistered `{!islaG Sigma} `{!threadG}
    args n payloadStart lengthBytes frameBytes (loaded : bv 64) prefix rest :
  ZesuEntryIntro (decodeItemEntryAt800d6ad8 args n payloadStart lengthBytes frameBytes loaded prefix rest) _ :=
  decodeItemEntry6ad8AdditionalIntroduction args n payloadStart lengthBytes frameBytes loaded prefix rest.

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

Require Export ZesuSsz.Compliance.DecodeItemCompletedFoldPureFacts.
