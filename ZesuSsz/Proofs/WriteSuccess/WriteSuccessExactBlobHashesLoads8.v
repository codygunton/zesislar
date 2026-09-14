Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
From IslaTraces.write_success_67 Require Import instrs.
Local Remove Hints IslaTraces.write_success_67.a15454_spec.a15454_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_67.a15458_spec.a15458_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_67.a1545c_spec.a1545c_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_67.a15460_spec.a15460_spec_inst : typeclass_instances.

Definition blobLoads8Entry `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x8", BitsShape 64); (KindReg "x9", BitsShape 64);
     (KindReg "x18", BitsShape 64); (KindReg "x26", BitsShape 64)] ∗
   "x19" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 12 <= length bytes)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobLoads8Entry) := I.

Definition blobLoads8Post `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x8" ↦ᵣ RVal_Bits (transactionRowByte bytes index 8) ∗
   "x9" ↦ᵣ RVal_Bits (transactionRowByte bytes index 9) ∗
   "x18" ↦ᵣ RVal_Bits (transactionRowByte bytes index 10) ∗
   "x26" ↦ᵣ RVal_Bits (transactionRowByte bytes index 11) ∗
   "x19" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 12 <= length bytes)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobLoads8Post) := I.

Lemma blob_loads8_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 (drop 8 IslaTraces.write_success_67.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15464 (blobLoads8Post row base bytes index P) -∗
  instr_body 0x15454 (blobLoads8Entry row base bytes index P).
Proof. zesu_block. all: unfold transactionRowByte; zesu_array_byte_value. Qed.
Print Assumptions blob_loads8_correct.
