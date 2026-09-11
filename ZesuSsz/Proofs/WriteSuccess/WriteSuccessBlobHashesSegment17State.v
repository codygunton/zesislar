Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopCommon.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.

Definition writeSuccessBlobHashesSegment17State
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessBlobHashesBodyOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x19" ↦ᵣ RVal_Bits pointer ∗
   "x27" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
   base ↦ₘ∗ bytes ∗ writeSuccessBlobHashesScratch sp ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeSuccessBlobHashesEvents sp (S remaining) tail) ∗ P ∗
   writeSuccessFixedWidthArrayInvariant
     sp pointer base total processed remaining bytes ∗
   instr_pre 0x15564
     (writeSuccessBlobHashesLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessBlobHashesSegment17State) := I.
