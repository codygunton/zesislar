Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Compliance.DecodeItemUnfoldRegistrations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.DecodeItemFrameImage.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ResultImage.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemJoinTransfers.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Require Import ZesuSsz.Compliance.DecodeItemRawOutputFacts.
From Coq Require Import List ZArith Lia.
Import ListNotations.
Open Scope Z_scope.

Require Import ZesuSsz.Compliance.DecodeItemOutputWitnessSelections.
Lemma decodeItemLiteralOutputCanonicalLookupNamed `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest :
  decodeItemInputHead args prefix rest ->
  bv_unsigned prefix <= 127 ->
  @ZesuCanonicalAnchor Sigma
    (decodeItemOutputPointer args ↦ₘ∗ decodeItemRawOutputStorage
      (decodeItemBeforeStorage args) (Z_to_bv 64 (decodeItemInputPointer args)) 1)
    (decodeItemJoin698cTarget args prefix rest true)
    (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemInputHead args prefix rest /\ bv_unsigned prefix <= 127 /\
      decodeItemAcceptedFacts args false 0 1⌝ ∗
     ∃ (a3 a4 a5 a6 : bv 64) (frameBytes : list byte),
       decodeItemReturnEntryCore args (decodeItemRawOutputLocals args
         (Z_to_bv 64 (decodeItemInputPointer args)) 1 a3 a4 a5 a6 1 frameBytes))%I.
Proof.
  intros Hhead Hclass.
  lazymatch goal with
  | |- ZesuCanonicalAnchor ?anchor _ _ =>
      let registered := constr:(_ : ZesuCanonicalAnchor anchor _ _) in
      exact registered
  end.
Qed.

Lemma decodeItemLiteralOutputCanonicalLookupExpanded `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest :
  decodeItemInputHead args prefix rest ->
  bv_unsigned prefix <= 127 ->
  @ZesuCanonicalAnchor Sigma
    (decodeItemOutputPointer args ↦ₘ∗ decodeItemRawOutputStorage
      (decodeItemBeforeStorage args) (Z_to_bv 64 (decodeItemInputPointer args)) 1)
    ((∃ (locals : DecodeItemReturnLocals) (pointerBytes lengthBytes : list byte),
      decodeItem698cCaseResources args locals pointerBytes lengthBytes prefix rest true)%I)
    (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemInputHead args prefix rest /\ bv_unsigned prefix <= 127 /\
      decodeItemAcceptedFacts args false 0 1⌝ ∗
     ∃ (a3 a4 a5 a6 : bv 64) (frameBytes : list byte),
       decodeItemReturnEntryCore args (decodeItemRawOutputLocals args
         (Z_to_bv 64 (decodeItemInputPointer args)) 1 a3 a4 a5 a6 1 frameBytes))%I.
Proof.
  intros Hhead Hclass.
  lazymatch goal with
  | |- ZesuCanonicalAnchor ?anchor _ _ =>
      let registered := constr:(_ : ZesuCanonicalAnchor anchor _ _) in
      exact registered
  end.
Qed.

Lemma decodeItemShortStringOutputCanonicalLookupNamed `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (payloadLength : bv 64) :
  decodeItemInputHead args prefix rest ->
  129 <= bv_unsigned prefix <= 183 ->
  bv_unsigned payloadLength = bv_unsigned prefix - 128 ->
  @ZesuCanonicalAnchor Sigma
    (decodeItemOutputPointer args ↦ₘ∗ decodeItemRawOutputStorage
      (decodeItemBeforeStorage args) (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) 1) payloadLength)
    (decodeItemJoin698cTarget args prefix rest false)
    (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemInputHead args prefix rest /\ 129 <= bv_unsigned prefix <= 183 /\
      bv_unsigned payloadLength = bv_unsigned prefix - 128 /\
      decodeItemAcceptedFacts args false 1 (bv_unsigned prefix - 128)⌝ ∗
     ∃ (a3 a4 a5 a6 : bv 64) (frameBytes : list byte),
       decodeItemReturnEntryCore args (decodeItemRawOutputLocals args
         (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) 1)
         (bv_add payloadLength 1) a3 a4 a5 a6 payloadLength frameBytes))%I.
Proof.
  intros Hhead Hclass Hlength.
  lazymatch goal with
  | |- ZesuCanonicalAnchor ?anchor _ _ =>
      let registered := constr:(_ : ZesuCanonicalAnchor anchor _ _) in
      exact registered
  end.
Qed.

Lemma decodeItemShortStringOutputCanonicalLookupExpanded `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (payloadLength : bv 64) :
  decodeItemInputHead args prefix rest ->
  129 <= bv_unsigned prefix <= 183 ->
  bv_unsigned payloadLength = bv_unsigned prefix - 128 ->
  @ZesuCanonicalAnchor Sigma
    (decodeItemOutputPointer args ↦ₘ∗ decodeItemRawOutputStorage
      (decodeItemBeforeStorage args) (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) 1) payloadLength)
    ((∃ (locals : DecodeItemReturnLocals) (pointerBytes lengthBytes : list byte),
      decodeItem698cCaseResources args locals pointerBytes lengthBytes prefix rest false)%I)
    (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemInputHead args prefix rest /\ 129 <= bv_unsigned prefix <= 183 /\
      bv_unsigned payloadLength = bv_unsigned prefix - 128 /\
      decodeItemAcceptedFacts args false 1 (bv_unsigned prefix - 128)⌝ ∗
     ∃ (a3 a4 a5 a6 : bv 64) (frameBytes : list byte),
       decodeItemReturnEntryCore args (decodeItemRawOutputLocals args
         (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) 1)
         (bv_add payloadLength 1) a3 a4 a5 a6 payloadLength frameBytes))%I.
Proof.
  intros Hhead Hclass Hlength.
  lazymatch goal with
  | |- ZesuCanonicalAnchor ?anchor _ _ =>
      let registered := constr:(_ : ZesuCanonicalAnchor anchor _ _) in
      exact registered
  end.
Qed.

Print Assumptions decodeItemLiteralOutputCanonicalLookupNamed.
Print Assumptions decodeItemLiteralOutputCanonicalLookupExpanded.
Print Assumptions decodeItemShortStringOutputCanonicalLookupNamed.
Print Assumptions decodeItemShortStringOutputCanonicalLookupExpanded.
