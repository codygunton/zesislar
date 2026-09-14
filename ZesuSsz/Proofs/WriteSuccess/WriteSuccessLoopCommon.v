Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsHashesLoop HintsBlobHashesLoop HintsStorageKeysLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccess.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Definition writeSuccessFixedWidthArrayInvariant `{!islaG Sigma}
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) : iProp Sigma :=
  (⌜total = (processed + S remaining)%nat⌝ ∗
   ⌜length bytes = (32 * total)%nat⌝ ∗
   ⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ ∗
   ⌜(S remaining < 2 ^ 64)%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜((mapRamBase defaultMap) <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1896 < (machineRamEnd defaultMap))%Z⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessFixedWidthArrayInvariant) := I.
