Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The goal keeps the signed comparison of 128-bit zero-extensions inside a
   decision and an `if`; the guard fact already holds the unsigned comparison
   inside `ite`. *)
Lemma guard_nested_decision_sub `{!islaG Sigma} `{!threadG} (m x : bv 64) (R : iProp Sigma) :
  ~ (bv_unsigned (bv_sub m (BV 64 3)) >=
     bv_unsigned (bv_sub (BV 64 56)
       (bv_zero_extend 64 (ite (bool_decide (bv_unsigned x < 128)) (BV 1 1) (BV 1 0))))) ->
  R -∗ (⌜bv_unsigned (bv_sub m (BV 64 3)) <
         bv_unsigned (bv_sub (BV 64 56) (bv_zero_extend 64
           (if bool_decide (bv_signed (bv_zero_extend 128 x) < bv_signed (BV 128 128))
            then BV 1 1 else BV 1 0)))⌝ ∗ R).
Proof. intros Hguard. iIntros "HR". zesu_block2. Qed.

(* The same with an xor size class and an extended register on both sides. *)
Lemma guard_nested_decision_xor `{!islaG Sigma} `{!threadG} (m x y : bv 64) (R : iProp Sigma) :
  ~ (bv_unsigned (bv_sub m (BV 64 3)) >=
     bv_unsigned (bv_xor
       (bv_zero_extend 64 (ite (bool_decide (bv_unsigned x < bv_unsigned y)) (BV 1 1) (BV 1 0)))
       (BV 64 1))) ->
  R -∗ (⌜bv_unsigned (bv_sub m (BV 64 3)) <
         bv_unsigned (bv_xor (bv_zero_extend 64
           (if bool_decide (bv_signed (bv_zero_extend 128 x) < bv_signed (bv_zero_extend 128 y))
            then BV 1 1 else BV 1 0)) (BV 64 1))⌝ ∗ R).
Proof. intros Hguard. iIntros "HR". zesu_block2. Qed.

(* A masked cast compared with 3: the fact states the mask at a width written
   as 8 * 8. *)
Lemma guard_masked_cast_width `{!islaG Sigma} `{!threadG} (z : Z) (R : iProp Sigma) :
  ~ (3 >= bv_unsigned (@bv_and (8 * 8) (Z_to_bv 64 z) (BV (8 * 8) 255))) ->
  R -∗ (⌜3 < bv_unsigned (bv_and (Z_to_bv 64 z) (BV 64 255))⌝ ∗ R).
Proof. intros Hguard. iIntros "HR". zesu_block2. Qed.

(* The same with the mask written as a cast of an integer in the fact. *)
Lemma guard_masked_cast_literal `{!islaG Sigma} `{!threadG} (z : Z) (R : iProp Sigma) :
  ~ (3 >= bv_unsigned (bv_and (Z_to_bv 64 z) (Z_to_bv 64 255))) ->
  R -∗ (⌜3 < bv_unsigned (bv_and (Z_to_bv 64 z) (BV 64 255))⌝ ∗ R).
Proof. intros Hguard. iIntros "HR". zesu_block2. Qed.

(* A remainder of a wrapped cast sum, from a divisibility fact and a range. *)
Lemma divisible_cast_sum_remainder `{!islaG Sigma} `{!threadG} (f : Z) (R : iProp Sigma) :
  (16 | f) -> 96 <= f < 2^64 ->
  R -∗ (⌜bv_unsigned (bv_add (Z_to_bv 64 f) (BV 64 (2^64 - 96))) mod 16 = 0⌝ ∗ R).
Proof. intros Hdivide Hrange. iIntros "HR". zesu_block2. Qed.
