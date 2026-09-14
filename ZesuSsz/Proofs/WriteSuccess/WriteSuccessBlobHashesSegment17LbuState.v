Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopCommon.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.

Definition writeSuccessBlobHashesSegment17LbuEntry
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  writeSuccessBlobHashesBodySpec P.

Definition writeSuccessBlobHashesSegment17LbuState
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8)) (tail : spec)
    (byte : bv 8) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col (delete 18%nat writeSuccessBlobHashesBodyOtherRegShapes) ∗
   "x21" ↦ᵣ RVal_Bits (bv_zero_extend 64 byte) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x19" ↦ᵣ RVal_Bits pointer ∗
   "x27" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
   base ↦ₘ∗ bytes ∗ writeSuccessBlobHashesScratch sp ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessBlobHashesEvents sp (S remaining) tail) ∗ P ∗
   writeSuccessFixedWidthArrayInvariant
     sp pointer base total processed remaining bytes ∗
   instr_pre 0x15564
     (writeSuccessBlobHashesLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessBlobHashesSegment17LbuEntry) := I.
Global Instance : LithiumUnfold (@writeSuccessBlobHashesSegment17LbuState) := I.
