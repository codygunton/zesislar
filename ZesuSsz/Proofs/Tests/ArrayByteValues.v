Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma test_array_byte_cursor (row : bv 64) (base : Z)
    (bytes : list (bv 8)) (index : nat) (byte : bv 8) :
  bv_unsigned row = (base + Z.of_nat index)%Z ->
  (0x20000000 <= base)%Z ->
  (base + Z.of_nat (length bytes) < 0x40000000)%Z ->
  (index + 283 <= length bytes)%nat ->
  bytes !! Z.to_nat ((bv_unsigned (row + BV 64 282)%bv - base) `div` 1) =
    Some byte ->
  bv_zero_extend 64 byte = Z_to_bv 64
    (little_endian_to_bv 8 (take 1 (drop (index + 282)%nat bytes))).
Proof. intros. zesu_array_byte_value. Qed.

Print Assumptions array_byte_lookup.
Print Assumptions test_array_byte_cursor.
