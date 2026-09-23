Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
From IslaTraces.write_success_56 Require Import instrs.

Definition accessListsStorageWholeCountJumpEntry `{!islaG Sigma} `{!threadG}
    (sp old_ra old_data : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits old_ra ∗ "x10" ↦ᵣ RVal_Bits old_data ∗
   (bv_unsigned sp + 1744) ↦ₘ∗ bytes ∗ ⌜length bytes = 40%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1784 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessListsStorageWholeCountJumpEntry) := I.

Definition accessListsStorageWholeCountJumpPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x1521c) ∗ "x10" ↦ᵣ RVal_Bits (transactionRowWord bytes 0 8) ∗
   (bv_unsigned sp + 1744) ↦ₘ∗ bytes ∗ ⌜length bytes = 40%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1784 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessListsStorageWholeCountJumpPost) := I.

Lemma access_lists_storage_whole_count_jump_correct `{!islaG Sigma} `{!threadG}
    sp old_ra old_data bytes (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_56.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15d10 (accessListsStorageWholeCountJumpPost sp bytes P) -∗
  instr_body 0x15210 (accessListsStorageWholeCountJumpEntry sp old_ra old_data bytes P).
Proof. move => *. zesu_block. Qed.
Print Assumptions access_lists_storage_whole_count_jump_correct.
