Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
From IslaTraces.write_success_29 Require Import instrs.

Definition transactionsIndexEntry `{!islaG Sigma} `{!threadG}
    (sp base cursor old10 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessTransactionsOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits old10 ∗
   "x11" ↦ᵣ RVal_Bits cursor ∗
   (bv_unsigned sp + 104) ↦ₘ base ∗
   (bv_unsigned sp + 120) ↦ₘ? 1776 ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionsIndexEntry) := I.

Definition transactionsIndexPost `{!islaG Sigma} `{!threadG}
    (sp base cursor : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessTransactionsOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits (base + cursor * BV 64 288)%bv ∗
   "x11" ↦ᵣ RVal_Bits base ∗
   (bv_unsigned sp + 104) ↦ₘ base ∗
   (bv_unsigned sp + 120) ↦ₘ? 128 ∗
   (bv_unsigned sp + 248) ↦ₘ cursor ∗
   (bv_unsigned sp + 256) ↦ₘ? 1640 ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionsIndexPost) := I.

Lemma transactions_index_prefix_correct `{!islaG Sigma} `{!threadG}
    sp base cursor old10 (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_29.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14f1c (transactionsIndexPost sp base cursor P) -∗
  instr_body 0x14f08 (transactionsIndexEntry sp base cursor old10 P).
Proof.
  zesu_block.
Qed.
Print Assumptions transactions_index_prefix_correct.

