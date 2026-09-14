Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
From IslaTraces.write_success_66 Require Import instrs.

Definition blobSaveLoads12Entry `{!islaG Sigma} `{!threadG}
    (row count : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x27", BitsShape 64); (KindReg "x23", BitsShape 64);
     (KindReg "x24", BitsShape 64)] ∗
   "x22" ↦ᵣ RVal_Bits count ∗ "x19" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 15 <= length bytes)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobSaveLoads12Entry) := I.

Definition blobSaveLoads12Post `{!islaG Sigma} `{!threadG}
    (row count : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x27" ↦ᵣ RVal_Bits count ∗
   "x22" ↦ᵣ RVal_Bits (transactionRowByte bytes index 12) ∗
   "x23" ↦ᵣ RVal_Bits (transactionRowByte bytes index 13) ∗
   "x24" ↦ᵣ RVal_Bits (transactionRowByte bytes index 14) ∗
   "x19" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 15 <= length bytes)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobSaveLoads12Post) := I.

Lemma blob_save_loads12_correct `{!islaG Sigma} `{!threadG}
    row count base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 (drop 20 IslaTraces.write_success_66.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15434 (blobSaveLoads12Post row count base bytes index P) -∗
  instr_body 0x15424 (blobSaveLoads12Entry row count base bytes index P).
Proof. zesu_block. all: unfold transactionRowByte; zesu_array_byte_value. Qed.
Print Assumptions blob_save_loads12_correct.
