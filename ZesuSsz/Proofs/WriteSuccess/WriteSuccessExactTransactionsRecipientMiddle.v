Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_31 Require Import instrs.

Definition transactionRecipientMiddleEntry `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x7", BitsShape 64); (KindReg "x28", BitsShape 64);
     (KindReg "x29", BitsShape 64); (KindReg "x30", BitsShape 64)] ∗
   "x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 272 <= length bytes)%nat⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientMiddleEntry) := I.

Definition transactionRecipientMiddlePost `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x7" ↦ᵣ RVal_Bits (transactionRowByte bytes index 268) ∗
   "x28" ↦ᵣ RVal_Bits (transactionRowByte bytes index 269) ∗
   "x29" ↦ᵣ RVal_Bits (transactionRowByte bytes index 270) ∗
   "x30" ↦ᵣ RVal_Bits (transactionRowByte bytes index 271) ∗
   "x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 272 <= length bytes)%nat⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientMiddlePost) := I.

Lemma transactions_recipient_middle_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_31.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14ff0 (transactionRecipientMiddlePost row base bytes index P) -∗
  instr_body 0x14fe0 (transactionRecipientMiddleEntry row base bytes index P).
Proof.
  zesu_block.
  all: unfold transactionRowByte; zesu_array_byte_value.
Qed.
Print Assumptions transactions_recipient_middle_correct.
