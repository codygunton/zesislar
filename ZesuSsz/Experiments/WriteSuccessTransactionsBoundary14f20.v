From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.

Import ListNotations.

Definition writeSuccessTransactionsAt14f20Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec) (word : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x25" ↦ᵣ RVal_Bits word ∗
    "x10" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ word ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ ([] : list (bv 8)) ∗
    (base + 288 * Z.of_nat (length processed) + 8) ↦ₘ∗
      drop 8 (writeSuccessTransactionBytes transaction) ∗
    ⌜word = Z_to_bv 64
      (little_endian_to_bv 8
        (take 8 (writeSuccessTransactionBytes transaction)))⌝ ∗
    writeSuccessTransactions14f1cFrame sp base transactions processed ∗
    writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt14f20Spec) := I.
