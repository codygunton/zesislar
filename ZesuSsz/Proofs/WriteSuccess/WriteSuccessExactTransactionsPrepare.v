Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
From Coq Require Import Lists.List ZArith.ZArith.
From IslaTraces.write_success_33 Require Import instrs.

Definition transactionPrepareEntry `{!islaG Sigma} `{!threadG}
    (sp row high : bv 64) (low : bv 32) (kind : bv 8)
    (base : Z) (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits row ∗ "x13" ↦ᵣ RVal_Bits high ∗
   "x14" ↦ᵣ RVal_Bits (bv_zero_extend 64 low) ∗
   "x11" ↦ᵣ RVal_Bits (bv_zero_extend 64 kind) ∗
   base ↦ₘ∗ bytes ∗ (bv_unsigned sp + 176) ↦ₘ? 8 ∗
   (bv_unsigned sp + 1648) ↦ₘ? 12 ∗ (bv_unsigned sp + 1744) ↦ₘ? 1 ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 264 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= base⌝ ∗
   ⌜base + Z.of_nat (length bytes) < 0x40000000⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1745 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionPrepareEntry) := I.

Definition transactionPreparePost `{!islaG Sigma} `{!threadG}
    (sp row high : bv 64) (low : bv 32) (kind : bv 8)
    (base : Z) (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits (sp + BV 64 1744)%bv ∗ "x13" ↦ᵣ RVal_Bits high ∗
   "x14" ↦ᵣ RVal_Bits (bv_zero_extend 64 low) ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 1) ∗ base ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 176) ↦ₘ (transactionRowWord bytes index 256) ∗
   (bv_unsigned sp + 1648) ↦ₘ high ∗
   (bv_unsigned sp + 1656) ↦ₘ low ∗ (bv_unsigned sp + 1744) ↦ₘ kind ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 264 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= base⌝ ∗
   ⌜base + Z.of_nat (length bytes) < 0x40000000⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1745 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionPreparePost) := I.

Lemma transactions_prepare_correct `{!islaG Sigma} `{!threadG}
    sp row high low kind base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_33.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x150e8 (transactionPreparePost sp row high low kind base bytes index P) -∗
  instr_body 0x150cc (transactionPrepareEntry sp row high low kind base bytes index P).
Proof. zesu_block. all: unfold transactionRowWord; reflexivity. Qed.
Print Assumptions transactions_prepare_correct.
