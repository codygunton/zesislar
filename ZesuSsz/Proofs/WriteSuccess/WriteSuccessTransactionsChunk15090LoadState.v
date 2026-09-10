From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15090.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15090LoadFrame.

Definition writeSuccessTransactions15090LoadState
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x15" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 120) ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     take 128
       (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
         transaction) ∗
   (base + 288 * Z.of_nat (length processed) + 128) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 128 ∗
   (base + 288 * Z.of_nat (length processed) + 136) ↦ₘ∗
     drop 136
       (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
         transaction) ∗
   writeSuccessTransactions15090LoadMachineFrame
     sp base transactions processed transaction ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts
     sp base transaction processed bytes ∗
   ⌜bv_unsigned
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Definition writeSuccessTransactions15090LoadResult
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (writeSuccessTransactionsMachine15090WithX15
     sp base transactions processed transaction
     (RVal_Bits
       (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
         transaction 128)) ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     take 128
       (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
         transaction) ∗
   (base + 288 * Z.of_nat (length processed) + 128) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 128 ∗
   (base + 288 * Z.of_nat (length processed) + 136) ↦ₘ∗
     drop 136
       (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
         transaction) ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts
     sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactions15090LoadState) := I.
Global Instance : LithiumUnfold (@writeSuccessTransactions15090LoadResult) := I.
