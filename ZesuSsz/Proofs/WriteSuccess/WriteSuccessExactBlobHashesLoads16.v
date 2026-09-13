Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
From IslaTraces.write_success_66 Require Import instrs.
Local Remove Hints IslaTraces.write_success_66.a153dc_spec.a153dc_spec_inst : typeclass_instances.

Definition blobLoads16Entry `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x6", BitsShape 64); (KindReg "x7", BitsShape 64);
     (KindReg "x28", BitsShape 64); (KindReg "x8", BitsShape 64)] ∗
   "x19" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 20 <= length bytes)%nat⌝ ∗ ⌜(0x20000000 <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobLoads16Entry) := I.

Definition blobLoads16Post `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x6" ↦ᵣ RVal_Bits (transactionRowByte bytes index 16) ∗
   "x7" ↦ᵣ RVal_Bits (transactionRowByte bytes index 17) ∗
   "x28" ↦ᵣ RVal_Bits (transactionRowByte bytes index 18) ∗
   "x8" ↦ᵣ RVal_Bits (transactionRowByte bytes index 19) ∗
   "x19" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 20 <= length bytes)%nat⌝ ∗ ⌜(0x20000000 <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobLoads16Post) := I.

Lemma blob_loads16_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 IslaTraces.write_success_66.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x153e4 (blobLoads16Post row base bytes index P) -∗
  instr_body 0x153d4 (blobLoads16Entry row base bytes index P).
Proof. zesu_block. all: unfold transactionRowByte; zesu_array_byte_value. Qed.
Print Assumptions blob_loads16_correct.
