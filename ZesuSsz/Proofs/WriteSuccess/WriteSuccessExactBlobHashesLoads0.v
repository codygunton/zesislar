Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
From IslaTraces.write_success_67 Require Import instrs.
From IslaTraces.write_success_68 Require Import instrs.
Local Remove Hints IslaTraces.write_success_67.a15490_spec.a15490_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_68.a15494_spec.a15494_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_68.a15498_spec.a15498_spec_inst : typeclass_instances.

Definition blobLoads0Entry `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x21", BitsShape 64); (KindReg "x22", BitsShape 64);
     (KindReg "x23", BitsShape 64); (KindReg "x26", BitsShape 64)] ∗
   "x19" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 4 <= length bytes)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobLoads0Entry) := I.

Definition blobLoads0Post `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x21" ↦ᵣ RVal_Bits (transactionRowByte bytes index 0) ∗
   "x22" ↦ᵣ RVal_Bits (transactionRowByte bytes index 1) ∗
   "x23" ↦ᵣ RVal_Bits (transactionRowByte bytes index 2) ∗
   "x26" ↦ᵣ RVal_Bits (transactionRowByte bytes index 3) ∗
   "x19" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 4 <= length bytes)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobLoads0Post) := I.

Lemma blob_loads0_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 2 (drop 22 IslaTraces.write_success_67.instrs.instr_map) ++ take 2 IslaTraces.write_success_68.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x1549c (blobLoads0Post row base bytes index P) -∗
  instr_body 0x1548c (blobLoads0Entry row base bytes index P).
Proof. zesu_block. all: unfold transactionRowByte; zesu_array_byte_value. Qed.
Print Assumptions blob_loads0_correct.
