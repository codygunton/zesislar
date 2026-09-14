Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixHashesModel.
From Coq Require Import Lists.List ZArith.ZArith.

Definition suffixLoopFacts (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (source : list (bv 8)) : Prop :=
  length source = (32 * total)%nat /\ (processed + S remaining = total)%nat /\
  bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z /\
  (Z.of_nat (S remaining) < 18446744073709551616)%Z /\
  bv_unsigned sp `mod` 8 = 0 /\ (0x20000000 <= bv_unsigned sp)%Z /\
  (bv_unsigned sp + 1776 < 0x40000000)%Z /\
  (0x20000000 <= base)%Z /\ (base + Z.of_nat (length source) < 0x40000000)%Z.

Definition suffixLoopScratch `{!islaG Sigma} (sp : bv 64) : iProp Sigma :=
  ((bv_unsigned sp + 1744) ↦ₘ? 8 ∗ (bv_unsigned sp + 1752) ↦ₘ? 8 ∗
   (bv_unsigned sp + 1760) ↦ₘ? 8 ∗ (bv_unsigned sp + 1768) ↦ₘ? 8 ∗ True)%I.
Global Instance : LithiumUnfold (@suffixLoopScratch) := I.

Definition suffixLoopExit `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (source : list (bv 8)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x158d4) ∗ "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   "x8" ↦ᵣ RVal_Bits (BV 64 0) ∗
   "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (base + Z.of_nat (length source))) ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> ["x10";"x11";"x12";"x13";"x14";"x15";"x16"]) ∗
   base ↦ₘ∗ source ∗ suffixLoopScratch sp ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace tail ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixLoopExit) := I.

Definition suffixLoopPayload `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (source : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> ["x10";"x11";"x12";"x13";"x14";"x15";"x16"]) ∗
   base ↦ₘ∗ source ∗ suffixLoopScratch sp ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeSuccessExactSuffixHashesEvents sp processed (S remaining) source tail) ∗ P ∗
   ⌜suffixLoopFacts sp pointer base total processed remaining source⌝ ∗
   instr_pre 0x158e0 (suffixLoopExit sp base source tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@suffixLoopPayload) := I.

Definition suffixLoopSpec `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total : nat) (source : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (processed remaining : nat) (pointer old_ra old5 : bv 64),
   reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits old_ra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗ "x9" ↦ᵣ RVal_Bits pointer ∗
   suffixLoopPayload sp pointer base total processed remaining source tail P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixLoopSpec) := I.

Definition suffixTailPayload `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (source : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x158d4) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> ["x10";"x11";"x12";"x13";"x14";"x15";"x16"]) ∗
   base ↦ₘ∗ source ∗ suffixLoopScratch sp ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeSuccessExactSuffixHashesEvents sp (S processed) remaining source tail) ∗ P ∗
   ⌜suffixLoopFacts sp pointer base total processed remaining source⌝ ∗
   instr_pre 0x158e0 (suffixLoopExit sp base source tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@suffixTailPayload) := I.
