Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
From Coq Require Import Lists.List ZArith.ZArith.
From IslaTraces.write_success_30 Require Import instrs.

Definition transactionRecipientLoadEntry `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x19", BitsShape 64); (KindReg "x20", BitsShape 64)] ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits row ∗
   "x11" ↦ᵣ RVal_Bits chain ∗ "x12" ↦ᵣ RVal_Bits chainTag ∗
   base ↦ₘ∗ bytes ∗ (bv_unsigned sp + 1664) ↦ₘ? 16 ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 268 <= length bytes)%nat⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜((mapRamBase defaultMap) <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1680 < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientLoadEntry) := I.

Definition transactionRecipientLoadPost `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x19" ↦ᵣ RVal_Bits (transactionRowByte bytes index 266) ∗
   "x20" ↦ᵣ RVal_Bits (transactionRowByte bytes index 267) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits row ∗
   "x11" ↦ᵣ RVal_Bits (transactionRowByte bytes index 264) ∗
   "x12" ↦ᵣ RVal_Bits (transactionRowByte bytes index 265) ∗
   base ↦ₘ∗ bytes ∗ (bv_unsigned sp + 1664) ↦ₘ chain ∗
   (bv_unsigned sp + 1672) ↦ₘ chainTag ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 268 <= length bytes)%nat⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜((mapRamBase defaultMap) <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1680 < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientLoadPost) := I.

Lemma transactions_recipient_loads_correct `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_30.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14fa8 (transactionRecipientLoadPost sp row chain chainTag base bytes index P) -∗
  instr_body 0x14f90 (transactionRecipientLoadEntry sp row chain chainTag base bytes index P).
Proof.
  zesu_block.
  all: unfold transactionRowByte; zesu_array_byte_value.
Qed.
Print Assumptions transactions_recipient_loads_correct.
