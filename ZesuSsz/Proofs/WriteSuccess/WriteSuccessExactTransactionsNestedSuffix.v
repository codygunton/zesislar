Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
From Coq Require Import Lists.List ZArith.ZArith.
From IslaTraces.write_success_33 Require Import instrs.

Definition transactionNestedSuffixEntry `{!islaG Sigma} `{!threadG}
    (sp row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits row ∗
   reg_col [(KindReg "x19", BitsShape 64); (KindReg "x12", BitsShape 64)] ∗
   base ↦ₘ∗ bytes ∗ (bv_unsigned sp + 136) ↦ₘ? 8 ∗
   (bv_unsigned sp + 160) ↦ₘ? 16 ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 256 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= base⌝ ∗
   ⌜base + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 176 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionNestedSuffixEntry) := I.

Definition transactionNestedSuffixPost `{!islaG Sigma} `{!threadG}
    (sp row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits row ∗
   "x19" ↦ᵣ RVal_Bits (transactionRowWord bytes index 224) ∗
   "x12" ↦ᵣ RVal_Bits (transactionRowWord bytes index 248) ∗
   base ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 136) ↦ₘ (transactionRowWord bytes index 232) ∗
   (bv_unsigned sp + 160) ↦ₘ (transactionRowWord bytes index 248) ∗
   (bv_unsigned sp + 168) ↦ₘ (transactionRowWord bytes index 240) ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 256 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= base⌝ ∗
   ⌜base + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 176 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionNestedSuffixPost) := I.

Lemma transactions_nested_suffix_correct `{!islaG Sigma} `{!threadG}
    sp row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_33.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x150cc (transactionNestedSuffixPost sp row base bytes index P) -∗
  instr_body 0x150b0 (transactionNestedSuffixEntry sp row base bytes index P).
Proof. zesu_block. all: unfold transactionRowWord; reflexivity. Qed.
Print Assumptions transactions_nested_suffix_correct.
