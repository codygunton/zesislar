Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_63 Require Import instrs.

Definition accessListsTailEntry `{!islaG Sigma} `{!threadG}
    (sp index old11 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x11" ↦ᵣ RVal_Bits old11 ∗ (bv_unsigned sp + 272) ↦ₘ index ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 280 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessListsTailEntry) := I.

Definition accessListsTailPost `{!islaG Sigma} `{!threadG}
    (sp index : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x11" ↦ᵣ RVal_Bits (index + BV 64 1)%bv ∗ (bv_unsigned sp + 272) ↦ₘ index ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 280 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessListsTailPost) := I.

Lemma access_lists_tail_correct `{!islaG Sigma} `{!threadG}
    sp index old11 (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_63.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x151d4 (accessListsTailPost sp index P) -∗
  instr_body 0x153b4 (accessListsTailEntry sp index old11 P).
Proof. zesu_block. Qed.
Print Assumptions access_lists_tail_correct.
