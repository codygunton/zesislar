Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15088.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15088LoadFrame.

Definition writeSuccessTransactions15088LoadState
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x15" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 112) ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     take 120
       (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
         transaction) ∗
   (base + 288 * Z.of_nat (length processed) + 120) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 120 ∗
   (base + 288 * Z.of_nat (length processed) + 128) ↦ₘ∗
     drop 128
       (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
         transaction) ∗
   writeSuccessTransactions15088LoadMachineFrame
     sp base transactions processed transaction ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts
     sp base transaction processed bytes ∗
   ⌜bv_unsigned
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Definition writeSuccessTransactions15088LoadResult
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (writeSuccessTransactionsMachine15088WithX15
     sp base transactions processed transaction
     (RVal_Bits
       (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
         transaction 120)) ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     take 120
       (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
         transaction) ∗
   (base + 288 * Z.of_nat (length processed) + 120) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 120 ∗
   (base + 288 * Z.of_nat (length processed) + 128) ↦ₘ∗
     drop 128
       (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
         transaction) ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts
     sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactions15088LoadState) := I.
Global Instance : LithiumUnfold (@writeSuccessTransactions15088LoadResult) := I.
