Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The guard fact holds an unsigned 64-bit comparison under `ite`, decided by
   the bare procedure `Z.lt_dec`. The goal holds the signed comparison of a
   128-bit zero-extension under `if`, decided by the resolved instance. Both
   sides subtract from the same masked cast. *)
Lemma guard_decision_instance_sub `{!islaG Sigma} `{!threadG} (z : Z) (x : bv 64) (R : iProp Sigma) :
  ~ (bv_unsigned (bv_sub (bv_and (Z_to_bv 64 z) (BV 64 63)) (BV 64 3)) >=
     bv_unsigned (bv_sub (BV 64 56)
       (bv_zero_extend 64 (ite (@bool_decide (bv_unsigned x < 128) (Z.lt_dec _ _)) (BV 1 1) (BV 1 0))))) ->
  R -∗ (⌜bv_unsigned (bv_sub (bv_and (Z_to_bv 64 z) (BV 64 63)) (BV 64 3)) <
         bv_unsigned (bv_sub (BV 64 56) (bv_zero_extend 64
           (if bool_decide (bv_signed (bv_zero_extend 128 x) < bv_signed (BV 128 128))
            then BV 1 1 else BV 1 0)))⌝ ∗ R).
Proof. intros Hguard. iIntros "HR". zesu_block2. Qed.

(* The same with two registers and an xor size class. *)
Lemma guard_decision_instance_xor `{!islaG Sigma} `{!threadG} (z : Z) (x y : bv 64) (R : iProp Sigma) :
  ~ (bv_unsigned (bv_sub (bv_and (Z_to_bv 64 z) (BV 64 63)) (BV 64 3)) >=
     bv_unsigned (bv_xor
       (bv_zero_extend 64 (ite (@bool_decide (bv_unsigned x < bv_unsigned y) (Z.lt_dec _ _)) (BV 1 1) (BV 1 0)))
       (BV 64 1))) ->
  R -∗ (⌜bv_unsigned (bv_sub (bv_and (Z_to_bv 64 z) (BV 64 63)) (BV 64 3)) <
         bv_unsigned (bv_xor (bv_zero_extend 64
           (if bool_decide (bv_signed (bv_zero_extend 128 x) < bv_signed (bv_zero_extend 128 y))
            then BV 1 1 else BV 1 0)) (BV 64 1))⌝ ∗ R).
Proof. intros Hguard. iIntros "HR". zesu_block2. Qed.
