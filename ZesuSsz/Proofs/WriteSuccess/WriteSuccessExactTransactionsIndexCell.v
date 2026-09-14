Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_29 Require Import instrs.

Definition transactionIndexCellEntry `{!islaG Sigma} `{!threadG}
    (sp base cursor old_data : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits old_data ∗ "x11" ↦ᵣ RVal_Bits cursor ∗
   (bv_unsigned sp + 104) ↦ₘ base ∗ (bv_unsigned sp + 248) ↦ₘ? 8 ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 256 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionIndexCellEntry) := I.

Definition transactionIndexCellPost `{!islaG Sigma} `{!threadG}
    (sp base cursor : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits (base + cursor * BV 64 288)%bv ∗
   "x11" ↦ᵣ RVal_Bits base ∗
   (bv_unsigned sp + 104) ↦ₘ base ∗ (bv_unsigned sp + 248) ↦ₘ cursor ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 256 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionIndexCellPost) := I.

Lemma transactions_index_cell_correct `{!islaG Sigma} `{!threadG}
    sp base cursor old_data (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 5 IslaTraces.write_success_29.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14f1c (transactionIndexCellPost sp base cursor P) -∗
  instr_body 0x14f08 (transactionIndexCellEntry sp base cursor old_data P).
Proof. zesu_block. Qed.
Print Assumptions transactions_index_cell_correct.
