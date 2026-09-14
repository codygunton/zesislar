Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
From IslaTraces.write_success_58 Require Import instrs.

Definition storageKeysLoads4Entry `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x15", BitsShape 64); (KindReg "x31", BitsShape 64);
     (KindReg "x30", BitsShape 64); (KindReg "x29", BitsShape 64)] ∗
   "x22" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 8 <= length bytes)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysLoads4Entry) := I.

Definition storageKeysLoads4Post `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x15" ↦ᵣ RVal_Bits (transactionRowByte bytes index 4) ∗
   "x31" ↦ᵣ RVal_Bits (transactionRowByte bytes index 5) ∗
   "x30" ↦ᵣ RVal_Bits (transactionRowByte bytes index 6) ∗
   "x29" ↦ᵣ RVal_Bits (transactionRowByte bytes index 7) ∗
   "x22" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 8 <= length bytes)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysLoads4Post) := I.

Lemma storage_keys_loads4_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 (drop 16 IslaTraces.write_success_58.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15278 (storageKeysLoads4Post row base bytes index P) -∗
  instr_body 0x15268 (storageKeysLoads4Entry row base bytes index P).
Proof. zesu_block. all: unfold transactionRowByte; zesu_array_byte_value. Qed.
Print Assumptions storage_keys_loads4_correct.
