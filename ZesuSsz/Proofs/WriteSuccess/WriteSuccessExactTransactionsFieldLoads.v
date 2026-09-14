Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
From IslaTraces.write_success_29 Require Import instrs.

Definition transactionFieldLoadEntry `{!islaG Sigma} `{!threadG}
    (sp row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x11", BitsShape 64); (KindReg "x12", BitsShape 64);
     (KindReg "x13", BitsShape 64); (KindReg "x26", BitsShape 64);
     (KindReg "x8", BitsShape 64)] ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 272) ↦ₘ? 8 ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 200 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜((mapRamBase defaultMap) <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 280 < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionFieldLoadEntry) := I.

Definition transactionFieldLoadPost `{!islaG Sigma} `{!threadG}
    (sp row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x11" ↦ᵣ RVal_Bits (transactionRowWord bytes index 160) ∗
   "x12" ↦ᵣ RVal_Bits (transactionRowWord bytes index 168) ∗
   "x13" ↦ᵣ RVal_Bits (transactionRowWord bytes index 176) ∗
   "x26" ↦ᵣ RVal_Bits (transactionRowWord bytes index 184) ∗
   "x8" ↦ᵣ RVal_Bits (transactionRowWord bytes index 192) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 272) ↦ₘ (transactionRowWord bytes index 176) ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 200 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜((mapRamBase defaultMap) <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 280 < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionFieldLoadPost) := I.

Lemma transactions_field_loads_correct `{!islaG Sigma} `{!threadG}
    sp row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_29.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14f5c (transactionFieldLoadPost sp row base bytes index P) -∗
  instr_body 0x14f44 (transactionFieldLoadEntry sp row base bytes index P).
Proof. zesu_block. Qed.
Print Assumptions transactions_field_loads_correct.
