Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayDynamicBounds.
Require Import isla.riscv64.riscv64.
Lemma test_dynamic_array_index (row offset limit : bv 64) base index count (bytes : list (bv 8)) :
  bv_unsigned row = (base + Z.of_nat index)%Z ->
  bv_unsigned limit = Z.of_nat count -> offset <> limit ->
  (bv_unsigned offset <= bv_unsigned limit)%Z ->
  (index + count <= length bytes)%nat ->
  ((mapRamBase defaultMap) <= base)%Z ->
  (base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z ->
  (Z.to_nat ((bv_unsigned (row + offset)%bv - base) `div` 1) < length bytes)%nat.
Proof. apply array_cursor_dynamic_index_lt. Qed.
Print Assumptions test_dynamic_array_index.
