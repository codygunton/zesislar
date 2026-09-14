Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From Coq Require Import Lists.List.
From IslaTraces.write_success_49 Require Import instrs.

Definition transactionValueJumpEntry `{!islaG Sigma} `{!threadG}
    (sp first second third fourth old_ra : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x18" ↦ᵣ RVal_Bits first ∗ "x20" ↦ᵣ RVal_Bits second ∗
   "x21" ↦ᵣ RVal_Bits fourth ∗ "x1" ↦ᵣ RVal_Bits old_ra ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)] ∗
   (bv_unsigned sp + 128) ↦ₘ third ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 136 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionValueJumpEntry) := I.

Definition transactionValueJumpPost `{!islaG Sigma} `{!threadG}
    (sp first second third fourth : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x18" ↦ᵣ RVal_Bits first ∗ "x20" ↦ᵣ RVal_Bits second ∗
   "x21" ↦ᵣ RVal_Bits fourth ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x151b4) ∗
   "x10" ↦ᵣ RVal_Bits first ∗ "x11" ↦ᵣ RVal_Bits second ∗
   "x12" ↦ᵣ RVal_Bits third ∗ "x13" ↦ᵣ RVal_Bits fourth ∗
   (bv_unsigned sp + 128) ↦ₘ third ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 136 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionValueJumpPost) := I.

Lemma transactions_value_jump_correct `{!islaG Sigma} `{!threadG}
    sp first second third fourth old_ra (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_49.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15cb0 (transactionValueJumpPost sp first second third fourth P) -∗
  instr_body 0x1519c (transactionValueJumpEntry sp first second third fourth old_ra P).
Proof. zesu_block. Qed.
Print Assumptions transactions_value_jump_correct.
