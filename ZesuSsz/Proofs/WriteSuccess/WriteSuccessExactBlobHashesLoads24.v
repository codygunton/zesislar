Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
From IslaTraces.write_success_66 Require Import instrs.

Definition blobLoads24Entry `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x11", BitsShape 64); (KindReg "x5", BitsShape 64);
     (KindReg "x17", BitsShape 64); (KindReg "x16", BitsShape 64)] ∗
   "x19" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 28 <= length bytes)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobLoads24Entry) := I.

Definition blobLoads24Post `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x11" ↦ᵣ RVal_Bits (transactionRowByte bytes index 24) ∗
   "x5" ↦ᵣ RVal_Bits (transactionRowByte bytes index 25) ∗
   "x17" ↦ᵣ RVal_Bits (transactionRowByte bytes index 26) ∗
   "x16" ↦ᵣ RVal_Bits (transactionRowByte bytes index 27) ∗
   "x19" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 28 <= length bytes)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobLoads24Post) := I.

Lemma blob_loads24_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 (drop 12 IslaTraces.write_success_66.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15414 (blobLoads24Post row base bytes index P) -∗
  instr_body 0x15404 (blobLoads24Entry row base bytes index P).
Proof. zesu_block. all: unfold transactionRowByte; zesu_array_byte_value. Qed.
Print Assumptions blob_loads24_correct.
