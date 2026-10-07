Require Import ZesuSsz.Automation.All.
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

Lemma decodeItemStoredWordBytes (value : bv 64) :
  bv_to_little_endian 8 8 (bv_unsigned value) = word64Bytes (bv_unsigned value).
Proof.
  unfold word64Bytes, bv_to_little_endian, Z_to_little_endian.
  cbn [List.seq List.map Z.iter]. cbn.
  rewrite !Z.shiftr_shiftr; try lia.
  cbn. rewrite Z.shiftr_0_r. rewrite !Z.land_ones; try lia.
  repeat apply f_equal2; try reflexivity; apply bv_eq;
    rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn;
    rewrite Z.mod_mod; try reflexivity; lia.
Qed.

Lemma decodeItemStoredWordValue (value : bv 64) :
  littleEndian (bv_to_little_endian 8 8 (bv_unsigned value)) = bv_unsigned value.
Proof.
  apply (littleEndian_machine_bytes 8%nat).
  change (8 * Z.of_nat 8) with 64.
  pose proof (bv_unsigned_in_range 64 value) as Hrange.
  unfold bv_modulus in Hrange. exact Hrange.
Qed.

Lemma decodeItemStoredPointerImage (pointer lengthValue : bv 64) (tail : list byte) :
  fieldImage (bv_to_little_endian 8 8 (bv_unsigned pointer) ++
    bv_to_little_endian 8 8 (bv_unsigned lengthValue) ++ tail) 0
    (bv_to_little_endian 8 8 (bv_unsigned pointer)).
Proof.
  change (fieldImage (([] : list byte) ++
    bv_to_little_endian 8 8 (bv_unsigned pointer) ++
    (bv_to_little_endian 8 8 (bv_unsigned lengthValue) ++ tail))
    (length ([] : list byte)) (bv_to_little_endian 8 8 (bv_unsigned pointer))).
  apply fieldImage_middle.
Qed.

Lemma decodeItemStoredLengthImage (pointer lengthValue : bv 64) (tail : list byte) :
  fieldImage (bv_to_little_endian 8 8 (bv_unsigned pointer) ++
    bv_to_little_endian 8 8 (bv_unsigned lengthValue) ++ tail) 8
    (bv_to_little_endian 8 8 (bv_unsigned lengthValue)).
Proof.
  replace 8%nat with (length (bv_to_little_endian 8 8 (bv_unsigned pointer))) by
    (rewrite length_bv_to_little_endian; lia).
  apply fieldImage_middle.
Qed.


Print Assumptions decodeItemStoredWordBytes.
Print Assumptions decodeItemStoredWordValue.
Print Assumptions decodeItemStoredPointerImage.
Print Assumptions decodeItemStoredLengthImage.

Definition decodeItemRawOutputStorage (before : list byte) (pointer lengthValue : bv 64) : list byte :=
  bv_to_little_endian 8 8 (bv_unsigned pointer) ++
  bv_to_little_endian 8 8 (bv_unsigned lengthValue) ++
  skipn (N.to_nat 8) (skipn (N.to_nat 8)
    (firstn 32 before ++ bv_to_little_endian 2 8 (bv_unsigned (0 : bv 16)) ++
      skipn (32 + N.to_nat 2) before)).

Definition decodeItemRawOutputLocals (args : DecodeItemArgs)
    (pointer consumed a3 a4 a5 a6 : bv 64) (lengthValue : bv 64) (frameBytes : list byte) :=
  {| returnA1 := pointer; returnA2 := consumed;
     returnA3 := a3; returnA4 := a4; returnA5 := a5; returnA6 := a6;
     returnStorage := decodeItemRawOutputStorage (decodeItemBeforeStorage args) pointer lengthValue;
     returnFrame := frameBytes |}.

Lemma decodeItemRawOutputStorageShape before pointer lengthValue :
  decodeItemRawOutputStorage before pointer lengthValue =
    bv_to_little_endian 8 8 (bv_unsigned pointer) ++
    bv_to_little_endian 8 8 (bv_unsigned lengthValue) ++
    skipn 16 (firstn 32 before ++ [Z_to_bv 8 0; Z_to_bv 8 0] ++ skipn 34 before).
Proof. unfold decodeItemRawOutputStorage. rewrite skipn_skipn. reflexivity. Qed.

Lemma decodeItemRawOutputIntroduction `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (isLiteral : bool) (pointer lengthValue consumed : bv 64) :
  (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
    decodeItemInputHead args prefix rest /\
    (if isLiteral then bv_unsigned prefix <= 127 else 129 <= bv_unsigned prefix <= 183) /\
    bv_unsigned pointer = (decodeItemInputPointer args + (if isLiteral then 0 else 1))%Z /\
    bv_unsigned lengthValue = (if isLiteral then 1 else bv_unsigned prefix - 128) /\
    bv_unsigned consumed = (if isLiteral then 1 else (1 + (bv_unsigned prefix - 128))%Z) /\
    decodeItemAcceptedFacts args false (if isLiteral then 0 else 1)
      (if isLiteral then 1 else bv_unsigned prefix - 128)⌝ ∗
   ∃ (a3 a4 a5 a6 : bv 64) (frameBytes : list byte),
     decodeItemReturnEntryCore args
       (decodeItemRawOutputLocals args pointer consumed a3 a4 a5 a6 lengthValue frameBytes))%I
  ⊢ decodeItemJoin698cTarget args prefix rest isLiteral.
Proof.
  iIntros "(%Hfacts & (%a3 & %a4 & %a5 & %a6 & %frameBytes & Hcore))".
  destruct Hfacts as (Hdomain & Hhead & Hclass & Hpointer & Hlength & Hconsumed & Haccepted).
  destruct (proj2 Hdomain) as (_ & Hbefore & _).
  assert (Hp : length (bv_to_little_endian 8 8 (bv_unsigned pointer)) = 8%nat) by
    (rewrite length_bv_to_little_endian; lia).
  assert (Hl : length (bv_to_little_endian 8 8 (bv_unsigned lengthValue)) = 8%nat) by
    (rewrite length_bv_to_little_endian; lia).
  unfold decodeItemJoin698cTarget.
  iExists (decodeItemRawOutputLocals args pointer consumed a3 a4 a5 a6 lengthValue frameBytes),
    (bv_to_little_endian 8 8 (bv_unsigned pointer)),
    (bv_to_little_endian 8 8 (bv_unsigned lengthValue)).
  unfold decodeItemEntryAt800d698c. iFrame "Hcore". iPureIntro.
  cbn [decodeItemRawOutputLocals returnA1 returnA2 returnStorage]. rewrite decodeItemRawOutputStorageShape.
  repeat split; try assumption.
  - rewrite decodeItemStoredWordValue. exact Hlength.
  - exact (proj1 Haccepted).
  - exact (proj2 Haccepted).
  - apply decodeItemStoredPointerImage.
  - apply decodeItemStoredLengthImage.
  - apply decodeItemRawOutputStatus; assumption.
  - apply decodeItemStoredWordBytes.
  - apply decodeItemRawOutputPad17; assumption.
  - apply decodeItemRawOutputPad34; assumption.
Qed.

#[export] Instance decodeItemLiteralOutputWitness `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest :
  @ZesuPureFactAnchor Sigma (decodeItemJoin698cTarget args prefix rest true)
    (decodeItemOutputPointer args ↦ₘ∗ decodeItemRawOutputStorage
      (decodeItemBeforeStorage args) (Z_to_bv 64 (decodeItemInputPointer args)) 1)
    (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemInputHead args prefix rest /\ bv_unsigned prefix <= 127 /\
      decodeItemAcceptedFacts args false 0 1⌝ ∗
     ∃ (a3 a4 a5 a6 : bv 64) (frameBytes : list byte),
       decodeItemReturnEntryCore args (decodeItemRawOutputLocals args
         (Z_to_bv 64 (decodeItemInputPointer args)) 1 a3 a4 a5 a6 1 frameBytes))%I.
Proof.
  unfold ZesuPureFactAnchor, ZesuPureFactIntro.
  iIntros "(%Hfacts & Hcore)".
  destruct Hfacts as (Hdomain & Hhead & Hclass & Haccepted).
  destruct (proj2 Hdomain) as (Hinput & Hbefore & Hp & Hl & Hnowrap & Hlayout).
  pose proof (decodeItemRawInputPointer args Hp Hl Hnowrap) as Hpointer.
  iApply (decodeItemRawOutputIntroduction args prefix rest true
    (Z_to_bv 64 (decodeItemInputPointer args)) 1 1 with "[Hcore]").
  iFrame. iPureIntro. cbn.
  repeat split; try assumption; try reflexivity;
    try exact (proj1 Haccepted); try exact (proj2 Haccepted).
  all: first [tauto | lia].
Qed.

Lemma decodeItemLiteralOutputWitnessCanonical `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest :
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
  unfold ZesuCanonicalAnchor.
  exact (decodeItemLiteralOutputWitness args prefix rest).
Qed.

#[export] Instance decodeItemShortStringOutputWitness `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (payloadLength : bv 64) :
  @ZesuPureFactAnchor Sigma (decodeItemJoin698cTarget args prefix rest false)
    (decodeItemOutputPointer args ↦ₘ∗ decodeItemRawOutputStorage
      (decodeItemBeforeStorage args) (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) 1) payloadLength)
    (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemInputHead args prefix rest /\ 129 <= bv_unsigned prefix <= 183 /\
      bv_unsigned payloadLength = bv_unsigned prefix - 128 /\
      decodeItemAcceptedFacts args false 1 (bv_unsigned prefix - 128)⌝ ∗
     ∃ (a3 a4 a5 a6 : bv 64) (frameBytes : list byte),
       decodeItemReturnEntryCore args (decodeItemRawOutputLocals args
         (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) 1)
         (bv_add payloadLength 1) a3 a4 a5 a6 payloadLength frameBytes))%I.
Proof.
  unfold ZesuPureFactAnchor, ZesuPureFactIntro.
  iIntros "(%Hfacts & Hcore)".
  destruct Hfacts as (Hdomain & Hhead & Hclass & Hlength & Haccepted).
  destruct (proj2 Hdomain) as (Hinput & Hbefore & Hp & Hl & Hnowrap & Hlayout).
  pose proof (decodeItemRawInputSuccessor args prefix rest Hhead Hinput Hp Hnowrap) as Hpointer.
  assert (Hbounds : 0 <= bv_unsigned payloadLength + 1 < bv_modulus 64) by
    (unfold bv_modulus; cbn; lia).
  assert (Hconsumed : bv_unsigned (bv_add payloadLength 1) = 1 + (bv_unsigned prefix - 128)).
  { replace (bv_add payloadLength 1) with
      (Z_to_bv 64 (bv_unsigned payloadLength + 1)) by bv_solve.
    rewrite (Z_to_bv_small 64 _ Hbounds). lia. }
  iApply (decodeItemRawOutputIntroduction args prefix rest false
    (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) 1) payloadLength
    (bv_add payloadLength 1) with "[Hcore]").
  iFrame. iPureIntro. cbn.
  repeat split; try assumption;
    try exact (proj1 Haccepted); try exact (proj2 Haccepted).
  all: first [tauto | lia].
Qed.

Lemma decodeItemShortStringOutputWitnessCanonical `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (payloadLength : bv 64) :
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
  unfold ZesuCanonicalAnchor.
  exact (decodeItemShortStringOutputWitness args prefix rest payloadLength).
Qed.

#[export] Hint Extern 1
  (@ZesuCanonicalAnchor ?Sigma
    (decodeItemOutputPointer ?args ↦ₘ∗ decodeItemRawOutputStorage
      (decodeItemBeforeStorage ?args) (Z_to_bv 64 (decodeItemInputPointer ?args)) 1)%I _ _) =>
  match goal with
  | Hhead : decodeItemInputHead args ?prefix ?rest,
    Hclass : bv_unsigned ?prefix <= 127 |- _ =>
    exact (@decodeItemLiteralOutputWitnessCanonical Sigma _ _ args prefix rest)
  end : typeclass_instances.

#[export] Hint Extern 1
  (@ZesuCanonicalAnchor ?Sigma
    (decodeItemOutputPointer ?args ↦ₘ∗ decodeItemRawOutputStorage
      (decodeItemBeforeStorage ?args) (bv_add (Z_to_bv 64 (decodeItemInputPointer ?args)) 1) ?payloadLength)%I _ _) =>
  match goal with
  | Hhead : decodeItemInputHead args ?prefix ?rest,
    Hclass : 129 <= bv_unsigned ?prefix <= 183,
    Hlength : bv_unsigned payloadLength = bv_unsigned ?prefix - 128 |- _ =>
    exact (@decodeItemShortStringOutputWitnessCanonical Sigma _ _ args prefix rest payloadLength)
  end : typeclass_instances.

Print Assumptions decodeItemRawOutputIntroduction.
Print Assumptions decodeItemLiteralOutputWitness.
Print Assumptions decodeItemShortStringOutputWitness.
Print Assumptions decodeItemLiteralOutputWitnessCanonical.
Print Assumptions decodeItemShortStringOutputWitnessCanonical.
