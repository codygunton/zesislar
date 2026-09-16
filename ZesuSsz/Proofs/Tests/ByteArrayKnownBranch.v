Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.

Lemma test_known_array_branch (base : bv 64) (bytes : list (bv 8))
    (value : bv 8)
    (Hbound : bv_unsigned base + 8 < 2 ^ 64)
    (Hknown : bytes !! 8%nat = Some (BV 8 0))
    (Hread : bytes !! Z.to_nat
      ((bv_unsigned (base + BV 64 8)%bv - bv_unsigned base) `div` 1) = Some value)
    (Hbranch : bv_zero_extend 64 value <> BV 64 0) : False.
Proof. zesu_finish_array_branch. Qed.

Print Assumptions test_known_array_branch.

Lemma test_known_array_nonzero_branch (base : bv 64) (bytes : list (bv 8))
    (tag value : bv 8)
    (Hbound : bv_unsigned base + 8 < 2 ^ 64)
    (Hknown : bytes !! 8%nat = Some tag)
    (Htag : tag <> BV 8 0)
    (Hread : bytes !! Z.to_nat
      ((bv_unsigned (base + BV 64 8)%bv - bv_unsigned base) `div` 1) = Some value)
    (Hbranch : bv_zero_extend 64 value = BV 64 0) : False.
Proof.
  set (extended := bv_zero_extend 64 value) in Hbranch.
  zesu_finish_array_branch.
Qed.

Print Assumptions test_known_array_nonzero_branch.
