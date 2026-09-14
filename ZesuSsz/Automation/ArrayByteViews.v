Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.

Lemma array_byte_default (bytes : list (bv 8)) (index : nat) :
  Z_to_bv 64 (little_endian_to_bv 8 (take 1 (drop index bytes))) =
    bv_zero_extend 64 (default (BV 8 0) (bytes !! index)).
Proof.
  destruct (nth_lookup_or_length bytes index (BV 8 0)) as [Hlookup | Hlength].
  - rewrite Hlookup. simpl. symmetry. apply array_byte_lookup. exact Hlookup.
  - rewrite (drop_ge bytes index Hlength) (lookup_ge_None_2 _ _ Hlength).
    cbn. bv_solve.
Qed.
Print Assumptions array_byte_default.

Ltac zesu_array_byte_register_views :=
  repeat iSelect (_ ↦ᵣ RVal_Bits
    (Z_to_bv 64 (little_endian_to_bv 8 (take 1 (drop _ _)))))%I
    ltac:(fun Hreg => iEval (rewrite array_byte_default) in Hreg).

