Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_74 Require Import instrs.

Definition authorizationZeroPost `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) tail (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗
   "x9" ↦ᵣ RVal_Bits pointer ∗ "x18" ↦ᵣ RVal_Bits (BV 64 0) ∗
   (bv_unsigned sp + 168) ↦ₘ pointer ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 176 < (machineRamEnd defaultMap)⌝ ∗ spec_trace tail ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationZeroPost) := I.

Definition authorizationZeroEntry `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) tail (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   reg_col [(KindReg "x8", BitsShape 64); (KindReg "x9", BitsShape 64)] ∗
   "x18" ↦ᵣ RVal_Bits (BV 64 0) ∗ (bv_unsigned sp + 168) ↦ₘ pointer ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 176 < (machineRamEnd defaultMap)⌝ ∗ spec_trace tail ∗ P ∗
   instr_pre 0x15620 (authorizationZeroPost sp pointer tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationZeroEntry) := I.

Lemma authorization_initial_zero `{!islaG Sigma} `{!threadG}
    sp pointer tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_74.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15584 (authorizationZeroEntry sp pointer tail P).
Proof. zesu_block. Qed.
Print Assumptions authorization_initial_zero.
