Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Lemma test_array_byte_default_literal (bytes : list (bv 8)) (byte : bv 8) :
  bytes !! Z.to_nat (bv_unsigned (BV 64 280) `div` 1) = Some byte ->
  bv_zero_extend 64 byte =
    bv_zero_extend 64 (default (BV 8 0) (bytes !! 280%nat)).
Proof. intros. zesu_finish. Qed.

Lemma test_array_byte_default_index (bytes : list (bv 8)) index (byte : bv 8) :
  bytes !! index = Some byte ->
  bv_zero_extend 64 byte =
    bv_zero_extend 64 (default (BV 8 0) (bytes !! index)).
Proof. intros. zesu_finish. Qed.

Print Assumptions test_array_byte_default_literal.
Print Assumptions test_array_byte_default_index.
