Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_56 Require Import instrs.

Definition accessListsStorageCountJumpEntry `{!islaG Sigma} `{!threadG}
    (sp count old_ra old_data : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits old_ra ∗ "x10" ↦ᵣ RVal_Bits old_data ∗
   (bv_unsigned sp + 1752) ↦ₘ count ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1760 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessListsStorageCountJumpEntry) := I.

Definition accessListsStorageCountJumpPost `{!islaG Sigma} `{!threadG}
    (sp count : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x1521c) ∗ "x10" ↦ᵣ RVal_Bits count ∗
   (bv_unsigned sp + 1752) ↦ₘ count ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1760 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessListsStorageCountJumpPost) := I.

Lemma access_lists_storage_count_jump_correct `{!islaG Sigma} `{!threadG}
    sp count old_ra old_data (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_56.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15d10 (accessListsStorageCountJumpPost sp count P) -∗
  instr_body 0x15210 (accessListsStorageCountJumpEntry sp count old_ra old_data P).
Proof. zesu_block. Qed.
Print Assumptions access_lists_storage_count_jump_correct.
