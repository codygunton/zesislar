Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From Coq Require Import Lists.List ZArith.ZArith.
From IslaTraces.write_success_30 Require Import instrs.

Definition transactionOptionPrefixEntry `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x16"; "x17"; "x5"; "x6"; "x7"]) ∗
   "x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 285 <= length bytes)%nat⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionOptionPrefixEntry) := I.

Definition transactionOptionPrefixPost `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x16" ↦ᵣ RVal_Bits (transactionRowByte bytes index 283) ∗
   "x17" ↦ᵣ RVal_Bits (transactionRowByte bytes index 284) ∗
   "x5" ↦ᵣ RVal_Bits (transactionRowByte bytes index 272) ∗
   "x6" ↦ᵣ RVal_Bits (transactionRowByte bytes index 273) ∗
   "x7" ↦ᵣ RVal_Bits (transactionRowByte bytes index 274) ∗
   "x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 285 <= length bytes)%nat⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionOptionPrefixPost) := I.

Lemma transactions_option_prefix_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_30.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14f7c (transactionOptionPrefixPost row base bytes index P) -∗
  instr_body 0x14f68 (transactionOptionPrefixEntry row base bytes index P).
Proof.
  zesu_block.
  all: unfold transactionRowByte; zesu_array_byte_value.
Qed.
Print Assumptions transactions_option_prefix_correct.
