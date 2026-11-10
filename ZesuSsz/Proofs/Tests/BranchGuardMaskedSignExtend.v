Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* Facts with wide constants over atoms that no guard below names. A
   whole-context solver reads all of them; a selected solver reads none. *)
Ltac add_wide_facts words count :=
  lazymatch count with
  | O => idtac
  | S ?remaining =>
      let fact := fresh "Hwide" in
      pose proof (Z.abs_nonneg (nth count words 0 * 18446744073709551616 +
        340282366920938463463374607431768211456)) as fact;
      add_wide_facts words remaining
  end.

(* A low mask over a masked sign-extended byte: the one-wrap range is proved
   from the byte's own facts after the byte cast, and the guard ends on the byte. *)
Lemma branch_guard_masked_sign_extended_byte (byte : bv 8) (words : list Z) :
  128 <= bv_unsigned byte <= 183 -> True.
Proof.
  intro Hbyte.
  add_wide_facts words constr:(200%nat).
  assert (SimplImpl
    (bv_unsigned (bv_and (bv_and (bv_sign_extend 64 byte) (BV 64 255)) (BV 64 127)) < 42)
    (bv_unsigned byte - 128 < 42))
    by ZesuSsz.Automation2.Hooks.zesu_branch_guard_simpl_impl.
  exact I.
Qed.

(* The masked sign-extended byte alone normalizes to the byte. *)
Lemma branch_guard_sign_extended_byte_mask (byte : bv 8) :
  SimplImpl (bv_unsigned (bv_and (bv_sign_extend 64 byte) (BV 64 255)) = 128)
    (bv_unsigned byte = 128).
Proof. ZesuSsz.Automation2.Hooks.zesu_branch_guard_simpl_impl. Qed.

(* Without the byte's range facts the one-wrap range is not provable, and the
   guard keeps the masked word instead of searching the wide facts. *)
Lemma branch_guard_masked_sign_extended_byte_unranged (byte : bv 8) (words : list Z) : True.
Proof.
  add_wide_facts words constr:(200%nat).
  Fail assert (SimplImpl
    (bv_unsigned (bv_and (bv_and (bv_sign_extend 64 byte) (BV 64 255)) (BV 64 127)) < 42)
    (bv_unsigned byte - 128 < 42))
    by ZesuSsz.Automation2.Hooks.zesu_branch_guard_simpl_impl.
  exact I.
Qed.
