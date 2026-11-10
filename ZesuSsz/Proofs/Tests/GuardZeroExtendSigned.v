Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A branch on an unsigned comparison leaves the negated signed comparison of
   the operands' 128-bit zero-extensions. The successor asks for the same
   bound as an unsigned comparison. This control closes on main. *)
Lemma guard_zero_extend_plain `{!islaG Sigma} `{!threadG} (a b : bv 64) (R : iProp Sigma) :
  ~ (bv_signed (bv_zero_extend 128 a) < bv_signed (bv_zero_extend 128 b)) ->
  R -∗ (⌜bv_unsigned b <= bv_unsigned a⌝ ∗ R).
Proof. intros Hguard. iIntros "HR". zesu_block2. Qed.

(* The goal spells an operand with an unevaluated sum of constants. *)
Lemma guard_zero_extend_goal_sum `{!islaG Sigma} `{!threadG} (a x : bv 64) (R : iProp Sigma) :
  ~ (bv_signed (bv_zero_extend 128 a) < bv_signed (bv_zero_extend 128 (bv_add x (BV 64 8)))) ->
  R -∗ (⌜bv_unsigned (bv_add x (bv_add (BV 64 3) (BV 64 5))) <= bv_unsigned a⌝ ∗ R).
Proof. intros Hguard. iIntros "HR". zesu_block2. Qed.

(* The guard spells the operand with the unevaluated sum. *)
Lemma guard_zero_extend_fact_sum `{!islaG Sigma} `{!threadG} (a x : bv 64) (R : iProp Sigma) :
  ~ (bv_signed (bv_zero_extend 128 a) <
     bv_signed (bv_zero_extend 128 (bv_add x (bv_add (BV 64 3) (BV 64 5))))) ->
  R -∗ (⌜bv_unsigned (bv_add x (BV 64 8)) <= bv_unsigned a⌝ ∗ R).
Proof. intros Hguard. iIntros "HR". zesu_block2. Qed.

(* The goal's operand holds an `if` whose condition a context fact decides. *)
Lemma guard_zero_extend_ite `{!islaG Sigma} `{!threadG} (a x y : bv 64) (R : iProp Sigma) :
  bv_unsigned y < 8 ->
  ~ (bv_signed (bv_zero_extend 128 a) < bv_signed (bv_zero_extend 128 (bv_add x (BV 64 16)))) ->
  R -∗ (⌜bv_unsigned (bv_add x (ite (bool_decide (bv_unsigned y < 8)) (BV 64 16) (BV 64 24))) <=
         bv_unsigned a⌝ ∗ R).
Proof. intros Hy Hguard. iIntros "HR". zesu_block2. Qed.

(* A lower bound on a masked value: the guard compares the zero-extensions of
   the masked value and of 3, and spells the masked value's offset as a sum. *)
Lemma guard_zero_extend_mask `{!islaG Sigma} `{!threadG} (x : bv 64) (R : iProp Sigma) :
  ~ (bv_signed (bv_zero_extend 128 (bv_and (bv_add x (bv_add (BV 64 1) (BV 64 2))) (BV 64 255))) <
     bv_signed (bv_zero_extend 128 (BV 64 3))) ->
  R -∗ (⌜3 <= bv_unsigned (bv_and (bv_add x (BV 64 3)) (BV 64 255))⌝ ∗ R).
Proof. intros Hguard. iIntros "HR". zesu_block2. Qed.
