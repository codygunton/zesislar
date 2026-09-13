Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From Coq Require Import Lists.List ZArith.ZArith.
From IslaTraces.write_success_30 Require Import instrs.

Definition transactionToTagEntry `{!islaG Sigma} `{!threadG}
    (sp row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col [(KindReg "x15", BitsShape 64)] ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 120) ↦ₘ? 8 ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 286 <= length bytes)%nat⌝ ∗
   ⌜(0x20000000 <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(0x20000000 <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 128 < 0x40000000)%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionToTagEntry) := I.

Definition transactionToTagPost `{!islaG Sigma} `{!threadG}
    (sp row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x15" ↦ᵣ RVal_Bits (transactionRowByte bytes index 285) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 120) ↦ₘ (transactionRowByte bytes index 285) ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 286 <= length bytes)%nat⌝ ∗
   ⌜(0x20000000 <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(0x20000000 <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 128 < 0x40000000)%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionToTagPost) := I.

Lemma transactions_to_tag_correct `{!islaG Sigma} `{!threadG}
    sp row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_30.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14fb8 (transactionToTagPost sp row base bytes index P) -∗
  instr_body 0x14fb0 (transactionToTagEntry sp row base bytes index P).
Proof.
  zesu_block.
  all: unfold transactionRowByte; zesu_array_byte_value.
Qed.
Print Assumptions transactions_to_tag_correct.
