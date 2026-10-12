Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.

Lemma decodeItemOutput24StoreIntroductionRegistered `{!islaG Sigma}
    args (storage : list byte) (continuation : nat -> iProp Sigma) :
  @ZesuPureFactIntro Sigma
    (⌜8%N = 8%N⌝ ∗ ∃ index : nat,
      ⌜Z.of_nat index = decodeItemOutputPointer args + 24 - decodeItemOutputPointer args⌝ ∗
      ⌜(index + N.to_nat 8 <= length storage)%nat⌝ ∗ continuation index)%I
    (⌜length storage = 40%nat⌝ ∗ ⌜0 <= decodeItemOutputPointer args⌝ ∗
      ⌜decodeItemOutputPointer args + 40 < RlpDecodeItem.word64Modulus⌝ ∗
      continuation 24%nat)%I.
Proof. typeclasses eauto. Qed.

Lemma decodeItemOutput24StoreIntroductionMissingLength `{!islaG Sigma}
    (args : DecodeItemArgs) (storage : list byte) (continuation : nat -> iProp Sigma)  : True.
Proof.
  let target := constr:(@ZesuPureFactIntro Sigma(⌜8%N = 8%N⌝ ∗ ∃ index : nat,
      ⌜Z.of_nat index = decodeItemOutputPointer args + 24 - decodeItemOutputPointer args⌝ ∗
      ⌜(index + N.to_nat 8 <= length storage)%nat⌝ ∗ continuation index)%I
    (⌜0 <= decodeItemOutputPointer args⌝ ∗
      ⌜decodeItemOutputPointer args + 40 < RlpDecodeItem.word64Modulus⌝ ∗
      continuation 24%nat)%I) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

Lemma decodeItemOutput24StoreIntroductionWrongWidth `{!islaG Sigma}
    (args : DecodeItemArgs) (storage : list byte) (continuation : nat -> iProp Sigma)  : True.
Proof.
  let target := constr:(@ZesuPureFactIntro Sigma(⌜64%N = 8%N⌝ ∗ ∃ index : nat,
      ⌜Z.of_nat index = decodeItemOutputPointer args + 24 - decodeItemOutputPointer args⌝ ∗
      ⌜(index + N.to_nat 8 <= length storage)%nat⌝ ∗ continuation index)%I
    (⌜length storage = 40%nat⌝ ∗ ⌜0 <= decodeItemOutputPointer args⌝ ∗
      ⌜decodeItemOutputPointer args + 40 < RlpDecodeItem.word64Modulus⌝ ∗
      continuation 24%nat)%I) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

Lemma decodeItemOutput32WordStoreIntroductionRegistered `{!islaG Sigma}
    args locals (continuation : nat -> iProp Sigma) :
  @ZesuPureFactIntro Sigma
    (⌜8%N = 8%N⌝ ∗ ∃ index : nat,
      ⌜Z.of_nat index = Z.sub (Z.add (decodeItemOutputPointer args) 32) (decodeItemOutputPointer args)⌝ ∗
      ⌜(index + N.to_nat 8 <= length (returnStorage locals))%nat⌝ ∗ continuation index)%I
    (⌜length (returnStorage locals) = 40%nat⌝ ∗ continuation 32%nat)%I.
Proof. typeclasses eauto. Qed.

Lemma decodeItemOutput32WordStoreIntroductionMissingLength `{!islaG Sigma}
    (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (continuation : nat -> iProp Sigma)  : True.
Proof.
  let target := constr:(@ZesuPureFactIntro Sigma(⌜8%N = 8%N⌝ ∗ ∃ index : nat,
      ⌜Z.of_nat index = Z.sub (Z.add (decodeItemOutputPointer args) 32) (decodeItemOutputPointer args)⌝ ∗
      ⌜(index + N.to_nat 8 <= length (returnStorage locals))%nat⌝ ∗ continuation index)%I
    (continuation 32%nat)%I) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

Lemma decodeItemOutput32WordStoreIntroductionWrongWidth `{!islaG Sigma}
    (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (continuation : nat -> iProp Sigma)  : True.
Proof.
  let target := constr:(@ZesuPureFactIntro Sigma(⌜64%N = 8%N⌝ ∗ ∃ index : nat,
      ⌜Z.of_nat index = Z.sub (Z.add (decodeItemOutputPointer args) 32) (decodeItemOutputPointer args)⌝ ∗
      ⌜(index + N.to_nat 8 <= length (returnStorage locals))%nat⌝ ∗ continuation index)%I
    (⌜length (returnStorage locals) = 40%nat⌝ ∗ continuation 32%nat)%I) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

Lemma decodeItemOutput32ShortStoreIntroductionRegistered `{!islaG Sigma}
    args locals (continuation : nat -> iProp Sigma) :
  @ZesuPureFactIntro Sigma
    (⌜8%N = 8%N⌝ ∗ ∃ index : nat,
      ⌜Z.of_nat index = Z.sub (Z.add (decodeItemOutputPointer args) 32) (decodeItemOutputPointer args)⌝ ∗
      ⌜(index + N.to_nat 2 <= length (returnStorage locals))%nat⌝ ∗ continuation index)%I
    (⌜length (returnStorage locals) = 40%nat⌝ ∗ continuation 32%nat)%I.
Proof. typeclasses eauto. Qed.

Lemma decodeItemOutput32ShortStoreIntroductionMissingLength `{!islaG Sigma}
    (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (continuation : nat -> iProp Sigma)  : True.
Proof.
  let target := constr:(@ZesuPureFactIntro Sigma(⌜8%N = 8%N⌝ ∗ ∃ index : nat,
      ⌜Z.of_nat index = Z.sub (Z.add (decodeItemOutputPointer args) 32) (decodeItemOutputPointer args)⌝ ∗
      ⌜(index + N.to_nat 2 <= length (returnStorage locals))%nat⌝ ∗ continuation index)%I
    (continuation 32%nat)%I) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

Lemma decodeItemOutput32ShortStoreIntroductionWrongWidth `{!islaG Sigma}
    (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (continuation : nat -> iProp Sigma)  : True.
Proof.
  let target := constr:(@ZesuPureFactIntro Sigma(⌜64%N = 8%N⌝ ∗ ∃ index : nat,
      ⌜Z.of_nat index = Z.sub (Z.add (decodeItemOutputPointer args) 32) (decodeItemOutputPointer args)⌝ ∗
      ⌜(index + N.to_nat 2 <= length (returnStorage locals))%nat⌝ ∗ continuation index)%I
    (⌜length (returnStorage locals) = 40%nat⌝ ∗ continuation 32%nat)%I) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

