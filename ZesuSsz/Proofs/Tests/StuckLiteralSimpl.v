Require Import isla.riscv64.riscv64.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Open Scope Z_scope.

(* Lithium's per-step simplification (Automation2/Hooks.v) folds the
   bitvector moduli while simpl runs. A branch fact whose comparison has a
   signed literal on one side is stuck on the other side; simpl leaves it as
   it is, and must not compute 2^128 to find that out. *)

(* The fact is unchanged: the same goal before and after. *)
Lemma stuck_signed_literal_unchanged (word : bv 64) :
  negb (bool_decide (bv_signed (BV 128 8) < bv_signed (bv_zero_extend 128 word))) = true -> True.
Proof.
  tryif progress liSimpl then fail "liSimpl changed a stuck branch fact" else idtac.
  lazymatch goal with
  | |- negb (bool_decide (bv_signed (BV 128 8) < bv_signed (bv_zero_extend 128 word))) = true -> True => idtac
  end.
  intros _. exact I.
Qed.

(* Folded moduli: the literal's signed value is not computed during simpl.
   Plain simpl reduces the comparison's decision to a match on the computed
   value; the folded run cannot get past `bv_half_modulus 128`. *)
Lemma folded_moduli_block_literal (z : Z) :
  negb (bool_decide (bv_signed (BV 128 8) < z)) = true -> True.
Proof.
  Fail with_strategy opaque [bv_modulus bv_half_modulus]
    (let value := eval hnf in (bv_signed (BV 128 8)) in
     lazymatch value with Zpos _ => idtac end).
  let value := eval hnf in (bv_signed (BV 128 8)) in
  lazymatch value with Zpos _ => idtac end.
  intros _. exact I.
Qed.

(* Simplification still makes progress where it did before. *)
Lemma simpl_still_reduces (word : bv 64) :
  length [word; word] = 2%nat.
Proof.
  progress liSimpl.
  lazymatch goal with |- 2%nat = 2%nat => reflexivity end.
Qed.
