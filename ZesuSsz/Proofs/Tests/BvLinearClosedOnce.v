(* The closedness test of the reflective linear normal form
   (ZesuSsz/Automation2/BvLinear.v, `zesu_bvlin_closed`) answers once. With a
   backtracking test, a false equation with k closed subterms was refused
   only after 2^k reifications: the refutation below ran past its 20 s bound
   (30 s with four closed terms fewer) (the
   region search of a return block meets one per wrong candidate region).
   The `Timeout` bounds the refusal; it takes milliseconds with the fix. *)
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.
From stdpp Require Import bitvector.definitions.
Require Import ZesuSsz.Automation2.BvLinear.
Require Import ZesuSsz.Automation2.All.

Section zesu_bv_linear_closed_once.
Local Open Scope Z_scope.
Variable (sp : bv 64).

(* False: the left side is sp - 136, the right side sp - 128. *)
Goal bv_add (bv_add (bv_add (bv_add sp (BV 64 18446744073709551216)) (BV 64 400))
    (BV 64 18446744073709551480)) (BV 64 0) =
  Z_to_bv 64 (bv_unsigned sp - 400 + 48 + 56 + 40 + 16 + 56 + 16 + 32 + 1 - 1 + 2 - 2 + Z.of_nat 8 * 1).
Proof.
  Timeout 20 (tryif zesu_bv_linear_bv then fail 0 "proved a false goal" else idtac).
Abort.

(* The true variant still closes: closed subterms are literals. *)
Goal bv_add (bv_add (bv_add (bv_add sp (BV 64 18446744073709551216)) (BV 64 400))
    (BV 64 18446744073709551480)) (BV 64 0) =
  Z_to_bv 64 (bv_unsigned sp - 400 + 48 + 56 + 40 + 16 + 56 + 16 + 32 + Z.of_nat 0 * 1).
Proof. zesu_bv_linear_bv. Qed.

(* A product of two atoms is no literal: it stays one atom. *)
Goal forall x : Z, bv_add (Z_to_bv 64 (x * x)) (BV 64 8) = Z_to_bv 64 (x * x + 8).
Proof. intros x. zesu_bv_linear_bv. Qed.

End zesu_bv_linear_closed_once.
