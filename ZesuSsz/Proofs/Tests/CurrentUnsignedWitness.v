Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.

Lemma preserve_map_current_unsigned (current : Z) :
  mapRamBase defaultMap <= current ->
  current + 288 < machineRamEnd defaultMap ->
  (bv_unsigned (Z_to_bv 64 current) = current ->
   bv_unsigned (Z_to_bv 64 current) = current).
Proof.
  intros Hlower Hupper.
  zesu_preserve_current_unsigned.
  exact H7.
Qed.
Print Assumptions preserve_map_current_unsigned.

Lemma preserve_existing_name (current : Z) :
  mapRamBase defaultMap <= current ->
  current + 288 < machineRamEnd defaultMap ->
  True ->
  (bv_unsigned (Z_to_bv 64 current) = current ->
   bv_unsigned (Z_to_bv 64 current) = current).
Proof.
  intros Hlower Hupper H7.
  Fail zesu_preserve_current_unsigned.
  intro Hcurrent. exact Hcurrent.
Qed.
Print Assumptions preserve_existing_name.
