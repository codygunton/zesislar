Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From Coq Require Import Lists.List ZArith.ZArith.
From IslaTraces.write_success_30 Require Import instrs.

Definition transactionOptionValuesEntry `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x28"; "x29"; "x30"; "x31"; "x18"]) ∗
   "x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 285 <= length bytes)%nat⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionOptionValuesEntry) := I.

Definition transactionOptionValuesPost `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x28" ↦ᵣ RVal_Bits (transactionRowByte bytes index 275) ∗
   "x29" ↦ᵣ RVal_Bits (transactionRowByte bytes index 276) ∗
   "x30" ↦ᵣ RVal_Bits (transactionRowByte bytes index 277) ∗
   "x31" ↦ᵣ RVal_Bits (transactionRowByte bytes index 278) ∗
   "x18" ↦ᵣ RVal_Bits (transactionRowByte bytes index 279) ∗
   "x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 285 <= length bytes)%nat⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionOptionValuesPost) := I.

Lemma transactions_option_values_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_30.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14f90 (transactionOptionValuesPost row base bytes index P) -∗
  instr_body 0x14f7c (transactionOptionValuesEntry row base bytes index P).
Proof.
  zesu_block.
  all: unfold transactionRowByte; zesu_array_byte_value.
Qed.
Print Assumptions transactions_option_values_correct.
