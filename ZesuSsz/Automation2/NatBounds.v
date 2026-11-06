From Coq Require Import ZArith.ZArith.

(* Keep large natural powers in binary arithmetic before invoking lia. *)
Ltac zesu_normalize_nat_powers :=
  repeat match goal with
  | H : (_ < Nat.pow _ _)%nat |- _ =>
      apply Nat2Z.inj_lt in H; rewrite Nat2Z.inj_pow in H
  | H : (_ <= Nat.pow _ _)%nat |- _ =>
      apply Nat2Z.inj_le in H; rewrite Nat2Z.inj_pow in H
  end.

(* Solvers use binary bounds and leave other proof goals unchanged. *)
Ltac zesu_normalize_binary_nat_hypotheses :=
  repeat match goal with
  | H : (_ <= _)%nat |- _ =>
      apply Nat2Z.inj_le in H;
      repeat first [rewrite Nat2Z.inj_mul in H | rewrite Nat2Z.inj_pow in H]
  | H : (_ < _)%nat |- _ =>
      apply Nat2Z.inj_lt in H;
      repeat first [rewrite Nat2Z.inj_mul in H | rewrite Nat2Z.inj_pow in H]
  end.

Ltac zesu_normalize_binary_nat_goal :=
  lazymatch goal with
  | |- (_ <= _)%nat =>
      apply Nat2Z.inj_le; repeat first [rewrite Nat2Z.inj_mul | rewrite Nat2Z.inj_pow]
  | |- (_ < _)%nat =>
      apply Nat2Z.inj_lt; repeat first [rewrite Nat2Z.inj_mul | rewrite Nat2Z.inj_pow]
  | _ => idtac
  end.
