Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
From IslaTraces.write_success_66 Require Import instrs.

Definition blobLoads20Entry `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x9", BitsShape 64); (KindReg "x18", BitsShape 64);
     (KindReg "x20", BitsShape 64); (KindReg "x21", BitsShape 64)] ∗
   "x19" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 24 <= length bytes)%nat⌝ ∗ ⌜(0x20000000 <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobLoads20Entry) := I.

Definition blobLoads20Post `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x9" ↦ᵣ RVal_Bits (transactionRowByte bytes index 20) ∗
   "x18" ↦ᵣ RVal_Bits (transactionRowByte bytes index 21) ∗
   "x20" ↦ᵣ RVal_Bits (transactionRowByte bytes index 22) ∗
   "x21" ↦ᵣ RVal_Bits (transactionRowByte bytes index 23) ∗
   "x19" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 24 <= length bytes)%nat⌝ ∗ ⌜(0x20000000 <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobLoads20Post) := I.

Lemma blob_loads20_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 (drop 4 IslaTraces.write_success_66.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x153f4 (blobLoads20Post row base bytes index P) -∗
  instr_body 0x153e4 (blobLoads20Entry row base bytes index P).
Proof. zesu_block. all: unfold transactionRowByte; zesu_array_byte_value. Qed.
Print Assumptions blob_loads20_correct.
