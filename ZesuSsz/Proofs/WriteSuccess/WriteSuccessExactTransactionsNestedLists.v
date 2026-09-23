Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
From Coq Require Import Lists.List ZArith.ZArith.
From IslaTraces.write_success_33 Require Import instrs.

Definition transactionNestedListsEntry `{!islaG Sigma} `{!threadG}
    (sp row recipient : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits row ∗ "x12" ↦ᵣ RVal_Bits recipient ∗
   reg_col [(KindReg "x22", BitsShape 64)] ∗ base ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 256) ↦ₘ? 16 ∗ (bv_unsigned sp + 1640) ↦ₘ? 8 ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 224 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= base⌝ ∗
   ⌜base + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1648 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionNestedListsEntry) := I.

Definition transactionNestedListsPost `{!islaG Sigma} `{!threadG}
    (sp row recipient : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits row ∗
   "x12" ↦ᵣ RVal_Bits (transactionRowWord bytes index 216) ∗
   "x22" ↦ᵣ RVal_Bits (transactionRowWord bytes index 200) ∗
   base ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 256) ↦ₘ (transactionRowWord bytes index 208) ∗
   (bv_unsigned sp + 264) ↦ₘ (transactionRowWord bytes index 216) ∗
   (bv_unsigned sp + 1640) ↦ₘ recipient ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 224 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= base⌝ ∗
   ⌜base + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1648 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionNestedListsPost) := I.

Lemma transactions_nested_lists_correct `{!islaG Sigma} `{!threadG}
    sp row recipient base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_33.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x150b0 (transactionNestedListsPost sp row recipient base bytes index P) -∗
  instr_body 0x15098 (transactionNestedListsEntry sp row recipient base bytes index P).
Proof. move => *. zesu_block. Qed.
Print Assumptions transactions_nested_lists_correct.
