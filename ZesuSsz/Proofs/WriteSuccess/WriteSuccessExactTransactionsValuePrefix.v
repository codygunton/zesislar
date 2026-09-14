Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
From IslaTraces.write_success_31 Require Import instrs.

Definition transactionValuePrefixEntry `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x27", BitsShape 64); (KindReg "x18", BitsShape 64);
     (KindReg "x20", BitsShape 64); (KindReg "x29", BitsShape 64)] ∗
   "x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 72 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionValuePrefixEntry) := I.

Definition transactionValuePrefixPost `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x27" ↦ᵣ RVal_Bits (transactionRowByte bytes index 32) ∗
   "x18" ↦ᵣ RVal_Bits (transactionRowWord bytes index 48) ∗
   "x20" ↦ᵣ RVal_Bits (transactionRowWord bytes index 56) ∗
   "x29" ↦ᵣ RVal_Bits (transactionRowWord bytes index 64) ∗
   "x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 72 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionValuePrefixPost) := I.

Lemma transactions_value_prefix_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_31.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15028 (transactionValuePrefixPost row base bytes index P) -∗
  instr_body 0x15018 (transactionValuePrefixEntry row base bytes index P).
Proof.
  zesu_block.
  all: first [unfold transactionRowWord; reflexivity |
    unfold transactionRowByte; zesu_array_byte_value].
Qed.
Print Assumptions transactions_value_prefix_correct.
