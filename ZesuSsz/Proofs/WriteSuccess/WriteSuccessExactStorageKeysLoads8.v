Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
From IslaTraces.write_success_59 Require Import instrs.
From IslaTraces.write_success_60 Require Import instrs.

Definition storageKeysLoads8Entry `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x8", BitsShape 64); (KindReg "x26", BitsShape 64);
     (KindReg "x1", BitsShape 64); (KindReg "x21", BitsShape 64)] ∗
   "x22" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 12 <= length bytes)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysLoads8Entry) := I.

Definition storageKeysLoads8Post `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x8" ↦ᵣ RVal_Bits (transactionRowByte bytes index 8) ∗
   "x26" ↦ᵣ RVal_Bits (transactionRowByte bytes index 9) ∗
   "x1" ↦ᵣ RVal_Bits (transactionRowByte bytes index 10) ∗
   "x21" ↦ᵣ RVal_Bits (transactionRowByte bytes index 11) ∗
   "x22" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 12 <= length bytes)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysLoads8Post) := I.

Lemma storage_keys_loads8_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 (drop 7 IslaTraces.write_success_59.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x152b4 (storageKeysLoads8Post row base bytes index P) -∗
  instr_body 0x152a4 (storageKeysLoads8Entry row base bytes index P).
Proof. zesu_block. all: unfold transactionRowByte; zesu_array_byte_value. Qed.
Print Assumptions storage_keys_loads8_correct.
