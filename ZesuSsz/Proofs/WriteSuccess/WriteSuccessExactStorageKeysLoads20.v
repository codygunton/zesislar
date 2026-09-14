Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
From IslaTraces.write_success_58 Require Import instrs.

Definition storageKeysLoads20Entry `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x8", BitsShape 64); (KindReg "x26", BitsShape 64);
     (KindReg "x9", BitsShape 64); (KindReg "x25", BitsShape 64)] ∗
   "x22" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 24 <= length bytes)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysLoads20Entry) := I.

Definition storageKeysLoads20Post `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x8" ↦ᵣ RVal_Bits (transactionRowByte bytes index 20) ∗
   "x26" ↦ᵣ RVal_Bits (transactionRowByte bytes index 21) ∗
   "x9" ↦ᵣ RVal_Bits (transactionRowByte bytes index 22) ∗
   "x25" ↦ᵣ RVal_Bits (transactionRowByte bytes index 23) ∗
   "x22" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 24 <= length bytes)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysLoads20Post) := I.

Lemma storage_keys_loads20_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 (drop 4 IslaTraces.write_success_58.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15248 (storageKeysLoads20Post row base bytes index P) -∗
  instr_body 0x15238 (storageKeysLoads20Entry row base bytes index P).
Proof. zesu_block. all: unfold transactionRowByte; zesu_array_byte_value. Qed.
Print Assumptions storage_keys_loads20_correct.
