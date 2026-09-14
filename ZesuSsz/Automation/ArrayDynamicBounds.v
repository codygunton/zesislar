Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayDynamicCursors.
From Coq Require Import ZArith.ZArith.
Lemma array_cursor_dynamic_index_lt (row offset limit : bv 64) base index count
    (bytes : list (bv 8)) :
  bv_unsigned row = (base + Z.of_nat index)%Z ->
  bv_unsigned limit = Z.of_nat count ->
  offset <> limit -> (bv_unsigned offset <= bv_unsigned limit)%Z ->
  (index + count <= length bytes)%nat ->
  ((mapRamBase defaultMap) <= base)%Z ->
  (base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z ->
  (Z.to_nat ((bv_unsigned (row + offset)%bv - base) `div` 1) < length bytes)%nat.
Proof.
  intros Hrow Hlimit Hne Hle Hbound Hlow Hhigh.
  have Hrange := array_cursor_dynamic_range row offset limit base index count bytes
    Hrow Hlimit Hne Hle Hbound Hlow Hhigh.
  rewrite Z.div_1_r. apply Nat2Z.inj_lt. rewrite Z2Nat.id; lia.
Qed.
Print Assumptions array_cursor_dynamic_index_lt.
