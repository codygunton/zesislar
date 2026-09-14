Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopCommon.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15Frame.

Definition writeSuccessStorageKeysLbuOuterFrame `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) (x19 sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8))
    (tail : spec) : iProp Sigma :=
  ("x19" ↦ᵣ RVal_Bits x19 ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x27" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
   writeSuccessStorageKeysScratch sp ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessStorageKeysEvents sp (S remaining) tail) ∗ P ∗
   writeSuccessFixedWidthArrayInvariant
     sp pointer base total processed remaining bytes ∗
   instr_pre 0x153b4
     (writeSuccessStorageKeysLoopExit x19 sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessStorageKeysLbuOuterFrame) := I.

Definition writeSuccessStorageKeysLbuState `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) (target : string) (index offset : nat)
    (x19 sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (byte : bv 8) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col (delete index writeSuccessStorageKeysOtherRegShapes) ∗
   (target ↦ᵣ: fun _ => True) ∗ "x22" ↦ᵣ RVal_Bits pointer ∗
   (bv_unsigned pointer + Z.of_nat offset) ↦ₘ byte ∗
   base ↦ₘ∗ take (32 * processed) bytes ∗
   bv_unsigned pointer ↦ₘ∗ take offset (drop (32 * processed) bytes) ∗
   (bv_unsigned pointer + Z.of_nat (S offset)) ↦ₘ∗
     drop (S offset) (drop (32 * processed) bytes) ∗
   ⌜drop (32 * processed) bytes !! offset = Some byte⌝ ∗
   ⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned pointer + Z.of_nat offset⌝ ∗
   ⌜bv_unsigned pointer + Z.of_nat offset < (machineRamEnd defaultMap)⌝ ∗
   writeSuccessStorageKeysLbuOuterFrame P x19 sp pointer base total processed
     remaining bytes tail)%I.

Global Instance : LithiumUnfold (@writeSuccessStorageKeysLbuState) := I.

Definition writeSuccessStorageKeysLbuResult `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) (target : string) (index offset : nat)
    (x19 sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (byte : bv 8) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col (delete index writeSuccessStorageKeysOtherRegShapes) ∗
   target ↦ᵣ RVal_Bits (bv_zero_extend 64 byte) ∗
   "x22" ↦ᵣ RVal_Bits pointer ∗
   (bv_unsigned pointer + Z.of_nat offset) ↦ₘ byte ∗
   base ↦ₘ∗ take (32 * processed) bytes ∗
   bv_unsigned pointer ↦ₘ∗ take offset (drop (32 * processed) bytes) ∗
   (bv_unsigned pointer + Z.of_nat (S offset)) ↦ₘ∗
     drop (S offset) (drop (32 * processed) bytes) ∗
   ⌜drop (32 * processed) bytes !! offset = Some byte⌝ ∗
   ⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ ∗
   writeSuccessStorageKeysLbuOuterFrame P x19 sp pointer base total processed
     remaining bytes tail)%I.

Global Instance : LithiumUnfold (@writeSuccessStorageKeysLbuResult) := I.

Definition writeSuccessStorageKeysLbuPrepared `{!islaG Sigma} `{!threadG}
    (x19 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col (delete 0%nat writeSuccessStorageKeysOtherRegShapes) ∗
    ("x1" ↦ᵣ: fun _ => True) ∗ "x22" ↦ᵣ RVal_Bits pointer ∗
    base ↦ₘ∗ bytes ∗
    writeSuccessStorageKeysLbuOuterFrame P x19 sp pointer base total processed
      remaining bytes tail ∗
    ⌜length bytes = (32 * (processed + S remaining))%nat⌝ ∗
    ⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ ∗
    ⌜(mapRamBase defaultMap) <= base⌝ ∗
    ⌜base + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝)%I.

Global Instance : LithiumUnfold (@writeSuccessStorageKeysLbuPrepared) := I.
