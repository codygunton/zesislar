Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
From IslaTraces.write_success_103 Require Import instrs.

Definition suffixLoads24Entry `{!islaG Sigma} `{!threadG}
    (pointer : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)] ∗
   "x9" ↦ᵣ RVal_Bits pointer ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned pointer = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 28 <= length bytes)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixLoads24Entry) := I.

Definition suffixLoads24Post `{!islaG Sigma} `{!threadG}
    (pointer : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x10" ↦ᵣ RVal_Bits (transactionRowByte bytes index 25) ∗
   "x11" ↦ᵣ RVal_Bits (transactionRowByte bytes index 24) ∗
   "x12" ↦ᵣ RVal_Bits (transactionRowByte bytes index 26) ∗
   "x13" ↦ᵣ RVal_Bits (transactionRowByte bytes index 27) ∗
   "x9" ↦ᵣ RVal_Bits pointer ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned pointer = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 28 <= length bytes)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixLoads24Post) := I.

Lemma suffix_loads24_correct `{!islaG Sigma} `{!threadG}
    pointer base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 IslaTraces.write_success_103.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15764 (suffixLoads24Post pointer base bytes index P) -∗
  instr_body 0x15754 (suffixLoads24Entry pointer base bytes index P).
Proof. zesu_block. all: unfold transactionRowByte; zesu_array_byte_value. Qed.
Print Assumptions suffix_loads24_correct.

