Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From Coq Require Import Lists.List.
From IslaTraces.write_success_54 Require Import instrs.

Definition accessListsCopyJumpEntry `{!islaG Sigma} `{!threadG}
    (sp base cursor old_index old_ra : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x11" ↦ᵣ RVal_Bits cursor ∗ "x1" ↦ᵣ RVal_Bits old_ra ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x12", BitsShape 64)] ∗
   (bv_unsigned sp + 256) ↦ₘ base ∗ (bv_unsigned sp + 272) ↦ₘ old_index ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 280 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessListsCopyJumpEntry) := I.

Definition accessListsCopyJumpPost `{!islaG Sigma} `{!threadG}
    (sp base cursor : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits (sp + BV 64 1744)%bv ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned base + 40 * bv_unsigned cursor)) ∗
   "x12" ↦ᵣ RVal_Bits (BV 64 40) ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x15200) ∗
   (bv_unsigned sp + 256) ↦ₘ base ∗ (bv_unsigned sp + 272) ↦ₘ cursor ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 280 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessListsCopyJumpPost) := I.

Lemma access_lists_copy_jump_correct `{!islaG Sigma} `{!threadG}
    sp base cursor old_index old_ra (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_54.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x101d4 (accessListsCopyJumpPost sp base cursor P) -∗
  instr_body 0x151dc (accessListsCopyJumpEntry sp base cursor old_index old_ra P).
Proof. zesu_block. Qed.
Print Assumptions access_lists_copy_jump_correct.
