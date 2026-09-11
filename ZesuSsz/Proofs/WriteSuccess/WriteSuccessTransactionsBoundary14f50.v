Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f4c.

Definition writeSuccessTransactions14f50Frame
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ
     Z_to_bv 64 (Z.of_nat (length transactions)) ∗
   (bv_unsigned sp + 120) ↦ₘ? 104 ∗
   (bv_unsigned sp + 224) ↦ₘ
     writeSuccessTransactionWord transaction 152 ∗
   (bv_unsigned sp + 232) ↦ₘ
     writeSuccessTransactionWord transaction 144 ∗
   (bv_unsigned sp + 240) ↦ₘ
     writeSuccessTransactionWord transaction 136 ∗
   (bv_unsigned sp + 248) ↦ₘ
     Z_to_bv 64 (Z.of_nat (length processed)) ∗
   (bv_unsigned sp + 248 + 8) ↦ₘ? 1640 ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   reg_col (delete 7%nat
     (delete 7%nat
       (delete 18%nat
         (delete 7%nat
           (delete 20%nat writeSuccessTransactions14f1cOtherRegShapes))))) ∗
   True)%I.

Global Typeclasses Opaque writeSuccessTransactions14f50Frame.

Definition writeSuccessTransactionsAt14f50Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x25" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 0) ∗
    "x24" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 8) ∗
    "x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 16) ∗
    "x23" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 24) ∗
    "x11" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 160) ∗
    "x12" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 168) ∗
    "x13" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 176) ∗
    "x10" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      take 176 (writeSuccessTransactionBytes transaction) ∗
    (base + 288 * Z.of_nat (length processed) + 176) ↦ₘ
      writeSuccessTransactionWord transaction 176 ∗
    (base + 288 * Z.of_nat (length processed) + 184) ↦ₘ∗
      drop 184 (writeSuccessTransactionBytes transaction) ∗
    writeSuccessTransactions14f50Frame
      sp base transactions processed transaction ∗
    writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt14f50Spec) := I.
