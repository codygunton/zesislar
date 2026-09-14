Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.allocator_get Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.

Definition mainAllocatorEntry `{!islaG Sigma} `{!threadG}
    (sp inputPointer inputSize : bv 64) : iProp Sigma :=
  (∃ (a0 a1 a2 a3 : bv 64),
   reg_col zesu_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits a0 ∗ "x11" ↦ᵣ RVal_Bits a1 ∗
   "x12" ↦ᵣ RVal_Bits a2 ∗ "x13" ↦ᵣ RVal_Bits a3 ∗
   bv_unsigned sp ↦ₘ inputPointer ∗ (bv_unsigned sp + 8) ↦ₘ inputSize ∗
   (bv_unsigned sp + 16) ↦ₘ? 8 ∗ (bv_unsigned sp + 24) ↦ₘ? 8 ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 24 < 0x40000000⌝ ∗ True)%I.

Definition mainAllocatorExit `{!islaG Sigma} `{!threadG}
    (sp inputPointer inputSize : bv 64) : iProp Sigma :=
  (reg_col zesu_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits (BV 64 0x2401a0b0) ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 0x177a8) ∗
   "x12" ↦ᵣ RVal_Bits inputPointer ∗ "x13" ↦ᵣ RVal_Bits inputSize ∗
   bv_unsigned sp ↦ₘ inputPointer ∗ (bv_unsigned sp + 8) ↦ₘ inputSize ∗
   (bv_unsigned sp + 16) ↦ₘ (BV 64 0x2401a0b0) ∗
   (bv_unsigned sp + 24) ↦ₘ (BV 64 0x177a8) ∗ True)%I.

Lemma main_allocator_get_correct_with_frame `{!islaG Sigma} `{!threadG}
    (sp inputPointer inputSize : bv 64) (P : iProp Sigma) :
  ([∗ list] i ∈ IslaTraces.allocator_get.instrs.instr_map,
    instr i.1 (Some i.2)) -∗
  instr_body 0x14cec (mainAllocatorExit sp inputPointer inputSize ∗ P ∗ True) -∗
  instr_body 0x14ccc (mainAllocatorEntry sp inputPointer inputSize ∗ P ∗ True).
Proof.
  unfold IslaTraces.allocator_get.instrs.instr_map, mainAllocatorEntry, mainAllocatorExit.
  zesu_block.
Qed.
Print Assumptions main_allocator_get_correct_with_frame.
