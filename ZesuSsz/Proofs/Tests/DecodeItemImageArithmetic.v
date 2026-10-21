Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Compliance.DecodeItemExitDataFacts.
Require Import ZesuSsz.Contracts.AbiBytes.
From Coq Require Import List ZArith.

Lemma exitImageLength (before : list byte) (value : Z) :
  length before = 40%nat ->
  length (word64Bytes value ++ drop 8 before) = 40%nat.
Proof. intros Hlength. decodeItemExitImageArithmetic. Qed.

Lemma exitImageSliceLength (before : list byte) (value : Z) :
  length before = 40%nat ->
  length (take 8 (drop 8 (word64Bytes value ++ drop 8 before))) = 8%nat.
Proof. intros Hlength. decodeItemExitImageArithmetic. Qed.

Lemma exitImageArithmeticNat (n m : nat) :
  (n <= m)%nat -> (n + 1 <= m + 1)%nat.
Proof. intros Hle. Fail reflexivity. decodeItemExitImageArithmetic. Qed.

Lemma exitImageArithmeticZ (n m : Z) :
  (n <= m)%Z -> (n + 1 <= m + 1)%Z.
Proof. intros Hle. Fail reflexivity. decodeItemExitImageArithmetic. Qed.

Goal forall n : nat, n = 0%nat.
Proof. intros n. Fail decodeItemExitImageArithmetic. Abort.

Print Assumptions exitImageLength.
Print Assumptions exitImageSliceLength.
Print Assumptions exitImageArithmeticNat.
Print Assumptions exitImageArithmeticZ.
