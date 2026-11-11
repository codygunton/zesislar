(* Tests for the reflective linear normal form (ZesuSsz/Automation2/BvLinear.v)
   and its fast path in the project's bv_solve and lia. *)
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Automation2.BvLinear.

Section zesu_bv_linear_tests.
Local Open Scope Z_scope.
Variables (p q : bv 64) (x : Z).

(* Modular equalities and disequalities need no range fact. *)
Goal bv_add (bv_add p (BV 64 16)) (BV 64 8) = bv_add p (BV 64 24).
Proof. zesu_bv_linear_bv. Qed.
Goal bv_add p (BV 64 8) <> bv_add p (BV 64 16).
Proof. zesu_bv_linear_bv. Qed.
Goal bv_sub (bv_add p q) q = p.
Proof. zesu_bv_linear_bv. Qed.
Goal bv_add p (bv_opp (BV 64 8)) = bv_sub p (BV 64 8).
Proof. zesu_bv_linear_bv. Qed.
Goal bv_shiftl p (BV 64 3) = bv_mul (BV 64 8) p.
Proof. zesu_bv_linear_bv. Qed.
Goal bv_add p (BV 64 18446744073709551615) = bv_sub p (BV 64 1).
Proof. zesu_bv_linear_bv. Qed.
Goal Z_to_bv 64 (x + 8) = bv_add (Z_to_bv 64 x) (BV 64 8).
Proof. zesu_bv_linear_bv. Qed.
Goal bv_add (Z_to_bv 64 (bv_unsigned p + 16)) (BV 64 8) = bv_add p (BV 64 24).
Proof. zesu_bv_linear_bv. Qed.
(* A product of two atoms is an atom. *)
Goal bv_add (bv_mul p q) (BV 64 1) = bv_add (BV 64 1) (bv_mul p q).
Proof. zesu_bv_linear_bv. Qed.

(* Integer goals that map back to bit vectors. *)
Goal bv_unsigned (bv_add p (BV 64 8)) = bv_unsigned (bv_add (bv_add p (BV 64 4)) (BV 64 4)).
Proof. zesu_bv_linear_with ltac:(lia). Qed.
Goal bv_unsigned (bv_add p (BV 64 8)) <> bv_unsigned (bv_add p (BV 64 16)).
Proof. zesu_bv_linear_with ltac:(lia). Qed.
Goal bv_unsigned (bv_add p (BV 64 8)) <> bv_unsigned p + 16.
Proof. zesu_bv_linear_with ltac:(lia). Qed.
Goal 0 <= x -> x + 8 < 18446744073709551616 -> bv_unsigned (bv_add (Z_to_bv 64 x) (BV 64 8)) = x + 8.
Proof. intros. zesu_bv_linear_with ltac:(lia). Qed.

(* False goals and goals outside the fragment fail. *)
Ltac zesu_bv_linear_lia := zesu_bv_linear_with ltac:(lia).
Goal bv_add p (BV 64 8) = p.
Proof. Fail zesu_bv_linear_bv. Abort.
Goal bv_add p (BV 64 8) <> bv_add q (BV 64 8).
Proof. Fail zesu_bv_linear_bv. Abort.
Goal bv_unsigned (bv_add (Z_to_bv 64 x) (BV 64 8)) = x + 8.
Proof. Fail zesu_bv_linear_lia. Abort.
Goal (bv_unsigned p <= bv_unsigned p + 1)%Z.
Proof. Fail zesu_bv_linear_lia. Abort.
(* A goal with an evar is left to the other solvers. *)
Goal exists y : bv 64, bv_add p (BV 64 8) = bv_add y (BV 64 8).
Proof. eexists. Fail zesu_bv_linear_lia. Abort.
End zesu_bv_linear_tests.

Section zesu_bv_linear_solver_tests.
Local Open Scope Z_scope.
Variables (p : bv 64) (x : Z).

(* The project's solvers take the fast path. *)
Goal bv_add (bv_add p (BV 64 16)) (BV 64 8) = bv_add p (BV 64 24).
Proof. bv_solve. Qed.
Goal bv_add p (BV 64 8) <> bv_add p (BV 64 16).
Proof. bv_solve. Qed.
Goal bv_unsigned (bv_add p (BV 64 8)) <> bv_unsigned (bv_add p (BV 64 16)).
Proof. lia. Qed.
Goal 0 <= x -> x + 8 < 18446744073709551616 ->
  bv_unsigned (bv_add (Z_to_bv 64 x) (BV 64 8)) = x + 8.
Proof. intros. ZesuSsz.Automation2.MemoryAddress.zesu_stack_arithmetic. Qed.
End zesu_bv_linear_solver_tests.
