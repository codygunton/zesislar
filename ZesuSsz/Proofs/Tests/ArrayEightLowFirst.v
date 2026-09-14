Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma test_array_eight_low_first_cursor (pointer : bv 64) (base : Z)
    (bytes : list (bv 8)) (index : nat) (b0 b1 b2 b3 b4 b5 b6 b7 : bv 8) :
  bv_unsigned pointer = (base + Z.of_nat index)%Z ->
  (0x20000000 <= base)%Z ->
  (base + Z.of_nat (length bytes) < 0x40000000)%Z ->
  (index + 32 <= length bytes)%nat ->
  bytes !! Z.to_nat ((bv_unsigned (pointer + BV 64 24)%bv - base) `div` 1) = Some b0 ->
  bytes !! Z.to_nat ((bv_unsigned (pointer + BV 64 25)%bv - base) `div` 1) = Some b1 ->
  bytes !! Z.to_nat ((bv_unsigned (pointer + BV 64 26)%bv - base) `div` 1) = Some b2 ->
  bytes !! Z.to_nat ((bv_unsigned (pointer + BV 64 27)%bv - base) `div` 1) = Some b3 ->
  bytes !! Z.to_nat ((bv_unsigned (pointer + BV 64 28)%bv - base) `div` 1) = Some b4 ->
  bytes !! Z.to_nat ((bv_unsigned (pointer + BV 64 29)%bv - base) `div` 1) = Some b5 ->
  bytes !! Z.to_nat ((bv_unsigned (pointer + BV 64 30)%bv - base) `div` 1) = Some b6 ->
  bytes !! Z.to_nat ((bv_unsigned (pointer + BV 64 31)%bv - base) `div` 1) = Some b7 ->
  (bv_or (bv_shiftl (bv_or (bv_or (bv_shiftl (bv_zero_extend 64 b7) (BV 64 24)) (bv_shiftl (bv_zero_extend 64 b6) (BV 64 16))) (bv_or (bv_shiftl (bv_zero_extend 64 b5) (BV 64 8)) (bv_zero_extend 64 b4))) (BV 64 32)) (bv_or (bv_or (bv_shiftl (bv_zero_extend 64 b1) (BV 64 8)) (bv_zero_extend 64 b0)) (bv_or (bv_shiftl (bv_zero_extend 64 b2) (BV 64 16)) (bv_shiftl (bv_zero_extend 64 b3) (BV 64 24))))) =
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (index + 24)%nat bytes))).
Proof. intros. zesu_array_eight_value. Qed.
Print Assumptions test_array_eight_low_first_cursor.

