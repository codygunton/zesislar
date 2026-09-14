From Coq Require Import ZArith.ZArith.

(* Keep large natural powers in binary arithmetic before invoking lia. *)
Ltac zesu_normalize_nat_powers :=
  repeat match goal with
  | H : (_ < Nat.pow _ _)%nat |- _ =>
      apply Nat2Z.inj_lt in H; rewrite Nat2Z.inj_pow in H
  | H : (_ <= Nat.pow _ _)%nat |- _ =>
      apply Nat2Z.inj_le in H; rewrite Nat2Z.inj_pow in H
  end.
