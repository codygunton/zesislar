Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Definition writeSuccessTransactions14f44CarrierScratch
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
   (bv_unsigned sp + 120) ↦ₘ? 104 ∗
   (bv_unsigned sp + 224) ↦ₘ writeSuccessTransactionWord transaction 152 ∗
   (bv_unsigned sp + 232) ↦ₘ writeSuccessTransactionWord transaction 144 ∗
   (bv_unsigned sp + 240) ↦ₘ writeSuccessTransactionWord transaction 136 ∗
   (bv_unsigned sp + 248) ↦ₘ Z_to_bv 64 (Z.of_nat processed) ∗
   (bv_unsigned sp + 256) ↦ₘ? 848 ∗
   writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items ∗
   (bv_unsigned sp + 1136) ↦ₘ? 608 ∗
   (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   (bv_unsigned sp + 1792) ↦ₘ? 104)%I.

Global Typeclasses Opaque writeSuccessTransactions14f44CarrierScratch.

Definition writeSuccessTransactionsAt14f44CarrierSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec)
      (first second third fourth : bv 64) (items : list ByteListItem),
    reg_col zesu_ram_sys_regs ∗
    "x25" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 0) ∗
    "x24" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 8) ∗
    "x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 16) ∗
    "x23" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 24) ∗
    "x11" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 152) ∗
    "x10" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    reg_col (delete 18%nat
      (delete 7%nat
        (delete 20%nat writeSuccessTransactions14f1cOtherRegShapes))) ∗
    writeSuccessTransactions14f44CarrierScratch sp base (length transactions)
      (length processed) transaction first second third fourth items ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      writeSuccessTransactionBytes transaction ∗
    writeSuccessTransactionsCurrentPhaseCarrierFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items ∗
    writeSuccessTransactionsLoadFacts sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt14f44CarrierSpec) := I.
