Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
From IslaTraces.write_success_32 Require Import instrs.

Definition transactionSignatureValuesEntry `{!islaG Sigma} `{!threadG}
    (sp row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits row ∗
   reg_col [(KindReg "x21", BitsShape 64); (KindReg "x16", BitsShape 64)] ∗
   base ↦ₘ∗ bytes ∗ (bv_unsigned sp + 144) ↦ₘ? 16 ∗
   (bv_unsigned sp + 216) ↦ₘ? 8 ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 104 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= base⌝ ∗
   ⌜base + Z.of_nat (length bytes) < 0x40000000⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 224 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureValuesEntry) := I.

Definition transactionSignatureValuesPost `{!islaG Sigma} `{!threadG}
    (sp row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits row ∗
   "x21" ↦ᵣ RVal_Bits (transactionRowWord bytes index 72) ∗
   "x16" ↦ᵣ RVal_Bits (transactionRowWord bytes index 96) ∗
   base ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 144) ↦ₘ (transactionRowWord bytes index 88) ∗
   (bv_unsigned sp + 152) ↦ₘ (transactionRowWord bytes index 80) ∗
   (bv_unsigned sp + 216) ↦ₘ (transactionRowWord bytes index 96) ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 104 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= base⌝ ∗
   ⌜base + Z.of_nat (length bytes) < 0x40000000⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 224 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureValuesPost) := I.

Lemma transactions_signature_values_correct `{!islaG Sigma} `{!threadG}
    sp row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_32.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15060 (transactionSignatureValuesPost sp row base bytes index P) -∗
  instr_body 0x15044 (transactionSignatureValuesEntry sp row base bytes index P).
Proof. zesu_block. all: unfold transactionRowWord; reflexivity. Qed.
Print Assumptions transactions_signature_values_correct.
