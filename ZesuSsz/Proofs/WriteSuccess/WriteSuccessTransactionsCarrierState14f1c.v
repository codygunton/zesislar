From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Definition writeSuccessTransactionsCurrentPhaseCarrierFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (base ↦ₘ∗ prefix ∗
   (base + 288 * Z.of_nat (length processed) + 288) ↦ₘ∗
     writeSuccessTransactionsBytes remaining ∗
   writeSuccessTransactionsProcessedOwn processed ∗
   writeSuccessByteArrayOwn (writeSuccessTransactionDataPointer transaction)
     (writeSuccessTransactionData transaction) ∗
   writeSuccessTransactionRestOwn transaction ∗
   writeSuccessTransactionsOwn remaining ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeSuccessTransactionPhaseEvents TransactionType sp transaction
     (writeSuccessTransactionsEvents sp remaining
       (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
         (byteListItemEvents (sp - BV 64 32)%bv items
           (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8) tail))))) ∗ P ∗
   writeSuccessTransactionsInvariant sp base transactions processed
     (transaction :: remaining) bytes prefix suffix ∗
   instr_pre writeSuccessTransactionsLoopExitAddress
     (writeSuccessTransactionsLoopCarrierExit P sp base transactions bytes tail
       first second third fourth items) ∗ True)%I.

Definition writeSuccessTransactionsMachine14f1cCarrier
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed : list writeSuccessTransaction)
  (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactionsOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 base) ∗
   writeSuccessTransactions14f1cCarrierScratch sp base (length transactions)
     (length processed) first second third fourth items ∗ True)%I.

Definition writeSuccessTransactionsAt14f1cCarrierSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec)
      (first second third fourth : bv 64) (items : list ByteListItem),
    writeSuccessTransactionsMachine14f1cCarrier sp base transactions processed
      first second third fourth items ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      writeSuccessTransactionBytes transaction ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ ([] : list (bv 8)) ∗
    writeSuccessTransactionsCurrentPhaseCarrierFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items ∗
    writeSuccessTransactionsLoadFacts sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsCurrentPhaseCarrierFrame) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsMachine14f1cCarrier) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt14f1cCarrierSpec) := I.
