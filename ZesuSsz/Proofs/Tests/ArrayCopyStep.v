Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayCopyStep.
Require Import isla.riscv64.riscv64.
Lemma test_array_copy_step (base : Z) start (source : list (bv 8))
    (src limit i : bv 64) (data : list (bv 8)) (byte : bv 8) :
  bv_unsigned src = (base + Z.of_nat start)%Z ->
  bv_unsigned limit = Z.of_nat (length data) ->
  (start + length data <= length source)%nat ->
  (bv_unsigned i <= bv_unsigned limit)%Z -> i <> limit ->
  ((mapRamBase defaultMap) <= base)%Z ->
  (base + Z.of_nat (length source) < (machineRamEnd defaultMap))%Z ->
  take (Z.to_nat (bv_unsigned i)) data = take (Z.to_nat (bv_unsigned i)) (drop start source) ->
  source !! Z.to_nat ((bv_unsigned (src + i)%bv - base) `div` 1) = Some byte ->
  take (Z.to_nat (bv_unsigned (i + BV 64 1)%bv))
    (<[Z.to_nat (bv_unsigned i `div` 1):=bv_extract 0 8 (bv_zero_extend 64 byte)]> data) =
  take (Z.to_nat (bv_unsigned (i + BV 64 1)%bv)) (drop start source).
Proof. apply array_copy_step. Qed.
Print Assumptions test_array_copy_step.
