Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
From IslaTraces.write_success_58 Require Import instrs.

Definition storageKeysLoads12Entry `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x24", BitsShape 64); (KindReg "x20", BitsShape 64);
     (KindReg "x18", BitsShape 64); (KindReg "x23", BitsShape 64)] ∗
   "x22" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 16 <= length bytes)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysLoads12Entry) := I.

Definition storageKeysLoads12Post `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x24" ↦ᵣ RVal_Bits (transactionRowByte bytes index 12) ∗
   "x20" ↦ᵣ RVal_Bits (transactionRowByte bytes index 13) ∗
   "x18" ↦ᵣ RVal_Bits (transactionRowByte bytes index 14) ∗
   "x23" ↦ᵣ RVal_Bits (transactionRowByte bytes index 15) ∗
   "x22" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 16 <= length bytes)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysLoads12Post) := I.

Lemma storage_keys_loads12_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 (drop 20 IslaTraces.write_success_58.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15288 (storageKeysLoads12Post row base bytes index P) -∗
  instr_body 0x15278 (storageKeysLoads12Entry row base bytes index P).
Proof. zesu_block. all: unfold transactionRowByte; zesu_array_byte_value. Qed.
Print Assumptions storage_keys_loads12_correct.
