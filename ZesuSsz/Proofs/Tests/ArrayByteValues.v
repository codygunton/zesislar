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

Lemma test_array_byte_pair (low high : bv 8) :
  bv_or (bv_shiftl (bv_zero_extend 64 high) (BV 64 8))
    (bv_zero_extend 64 low) =
  Z_to_bv 64 (little_endian_to_bv 8 [low; high]).
Proof. apply array_byte_pair. Qed.

Print Assumptions array_byte_pair.
Lemma test_array_byte_pair_value (low high : bv 8) :
  bv_or (Z_to_bv 64 (bv_unsigned high * 256)) (bv_zero_extend 64 low) =
    Z_to_bv 64 (bv_unsigned low + bv_unsigned high * 256).
Proof. apply array_byte_pair_value. Qed.

Lemma test_array_byte_pair_value16 (low high : bv 8) :
  bv_or (Z_to_bv 64 (bv_unsigned high * 16777216))
    (Z_to_bv 64 (bv_unsigned low * 65536)) =
  Z_to_bv 64 (bv_unsigned low * 65536 + bv_unsigned high * 16777216).
Proof. apply array_byte_pair_value16. Qed.

Print Assumptions array_byte_pair_value.
Print Assumptions array_byte_pair_value16.
Print Assumptions test_array_byte_pair_value.
Print Assumptions test_array_byte_pair_value16.
Print Assumptions test_array_byte_pair.
Print Assumptions array_byte_lookup.
Print Assumptions test_array_byte_cursor.
