Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.

Lemma test_finish_large_nat_bound (sp : bv 64) (count : nat) :
  (count < 2 ^ 64)%nat ->
  bv_unsigned sp + 1896 < (machineRamEnd defaultMap) ->
  bv_unsigned sp - 32 + 32 < 2 ^ 64 /\ bv_unsigned sp + 0 < 2 ^ 64.
Proof. intros Hcount Hhigh. zesu_finish. Qed.
Print Assumptions test_finish_large_nat_bound.
