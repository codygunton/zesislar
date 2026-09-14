Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.

Lemma array_byte_pair_encoding (low high : bv 8) :
  Z_to_bv 64 (little_endian_to_bv 8 [low; high]) =
  Z_to_bv 64 (bv_unsigned low + bv_unsigned high * 256).
Proof. rewrite -array_byte_pair_shift_value array_byte_pair. reflexivity. Qed.
Print Assumptions array_byte_pair_encoding.

Ltac zesu_array_byte_pair_register_views :=
  repeat iSelect (_ ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [_; _])))%I
    ltac:(fun Hreg => iEval (rewrite array_byte_pair_encoding) in Hreg).

