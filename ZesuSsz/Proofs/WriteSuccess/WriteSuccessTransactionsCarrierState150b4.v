Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14fc8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15028.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15098.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.

Import ListNotations.

Definition writeSuccessTransactions150b4CarrierScratch
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
   (bv_unsigned sp + 120) ↦ₘ
     bv_zero_extend 64 (writeSuccessTransactionByte transaction 285) ∗
   (bv_unsigned sp + 128) ↦ₘ? 16 ∗
   (bv_unsigned sp + 144) ↦ₘ writeSuccessTransactionWord transaction 88 ∗
   (bv_unsigned sp + 152) ↦ₘ writeSuccessTransactionWord transaction 80 ∗
   (bv_unsigned sp + 160) ↦ₘ? 24 ∗
   (bv_unsigned sp + 184) ↦ₘ writeSuccessTransactionWord transaction 120 ∗
   (bv_unsigned sp + 192) ↦ₘ writeSuccessTransactionWord transaction 112 ∗
   (bv_unsigned sp + 200) ↦ₘ writeSuccessTransactionWord transaction 104 ∗
   (bv_unsigned sp + 208) ↦ₘ writeSuccessTransactionWord transaction 128 ∗
   (bv_unsigned sp + 216) ↦ₘ writeSuccessTransactionWord transaction 96 ∗
   (bv_unsigned sp + 224) ↦ₘ writeSuccessTransactionWord transaction 152 ∗
   (bv_unsigned sp + 232) ↦ₘ writeSuccessTransactionWord transaction 144 ∗
   (bv_unsigned sp + 240) ↦ₘ writeSuccessTransactionWord transaction 136 ∗
   (bv_unsigned sp + 248) ↦ₘ Z_to_bv 64 (Z.of_nat processed) ∗
   (bv_unsigned sp + 256) ↦ₘ writeSuccessTransactionWord transaction 208 ∗
   (bv_unsigned sp + 264) ↦ₘ writeSuccessTransactionWord transaction 216 ∗
   (bv_unsigned sp + 272) ↦ₘ writeSuccessTransactionWord transaction 176 ∗
   (bv_unsigned sp + 280) ↦ₘ? 824 ∗
   writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items ∗
   (bv_unsigned sp + 1136) ↦ₘ? 504 ∗
   (bv_unsigned sp + 1640) ↦ₘ
     writeSuccessTransactions15098X12 transaction ∗
   (bv_unsigned sp + 1648) ↦ₘ? 16 ∗
   (bv_unsigned sp + 1664) ↦ₘ writeSuccessTransactionWord transaction 160 ∗
   (bv_unsigned sp + 1672) ↦ₘ writeSuccessTransactionWord transaction 168 ∗
   (bv_unsigned sp + 1680) ↦ₘ? 64 ∗
   (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   (bv_unsigned sp + 1792) ↦ₘ? 104)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactions150b4CarrierScratch) := I.
Global Typeclasses Opaque writeSuccessTransactions150b4CarrierScratch.

Definition writeSuccessTransactions15078Upper
    (transaction : writeSuccessTransaction) : bv 64 :=
  bv_shiftl
    (bv_or
      (bv_or
        (bv_shiftl
          (bv_zero_extend 64 (writeSuccessTransactionByte transaction 272))
          (BV 64 24))
        (bv_shiftl
          (bv_zero_extend 64 (writeSuccessTransactionByte transaction 271))
          (BV 64 16)))
      (bv_or
        (bv_shiftl
          (bv_zero_extend 64 (writeSuccessTransactionByte transaction 270))
          (BV 64 8))
        (bv_zero_extend 64 (writeSuccessTransactionByte transaction 269))))
    (BV 64 32).

Definition writeSuccessTransactions150b4X12
    (transaction : writeSuccessTransaction) : bv 64 :=
  bv_or
    (writeSuccessTransactions15078Upper transaction)
    (bv_or
      (bv_or
        (bv_shiftl
          (bv_zero_extend 64 (writeSuccessTransactionByte transaction 268))
          (BV 64 24))
        (bv_shiftl
          (bv_zero_extend 64 (writeSuccessTransactionByte transaction 267))
          (BV 64 16)))
      (bv_or
        (bv_shiftl
          (bv_zero_extend 64 (writeSuccessTransactionByte transaction 266))
          (BV 64 8))
        (bv_zero_extend 64 (writeSuccessTransactionByte transaction 265)))).

Definition writeSuccessTransactionsMachine150b4Carrier `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col (delete 3%nat (delete 3%nat writeSuccessTransactions15028OtherRegShapes)) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64 (writeSuccessTransactionByte transaction 272))
         (BV 64 24))
       (bv_shiftl
         (bv_zero_extend 64 (writeSuccessTransactionByte transaction 271))
         (BV 64 16))) ∗
   "x6" ↦ᵣ RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64 (writeSuccessTransactionByte transaction 278))
         (BV 64 8))
       (bv_zero_extend 64 (writeSuccessTransactionByte transaction 277))) ∗
   "x7" ↦ᵣ RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64 (writeSuccessTransactionByte transaction 268))
         (BV 64 24))
       (bv_shiftl
         (bv_zero_extend 64 (writeSuccessTransactionByte transaction 267))
         (BV 64 16))) ∗
   "x8" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 192) ∗
   "x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 16) ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
   "x11" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 264)) ∗
   "x12" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 216) ∗
   "x13" ↦ᵣ RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_or
           (bv_or
             (bv_shiftl
               (bv_zero_extend 64 (writeSuccessTransactionByte transaction 280))
               (BV 64 24))
             (bv_shiftl
               (bv_zero_extend 64 (writeSuccessTransactionByte transaction 279))
               (BV 64 16)))
           (bv_or
             (bv_shiftl
               (bv_zero_extend 64 (writeSuccessTransactionByte transaction 278))
               (BV 64 8))
             (bv_zero_extend 64 (writeSuccessTransactionByte transaction 277))))
         (BV 64 32))
       (bv_or
         (bv_or
           (bv_shiftl
             (bv_zero_extend 64 (writeSuccessTransactionByte transaction 276))
             (BV 64 24))
           (bv_shiftl
             (bv_zero_extend 64 (writeSuccessTransactionByte transaction 275))
             (BV 64 16)))
         (bv_or
           (bv_shiftl
             (bv_zero_extend 64 (writeSuccessTransactionByte transaction 274))
             (BV 64 8))
           (bv_zero_extend 64 (writeSuccessTransactionByte transaction 273))))) ∗
   "x14" ↦ᵣ RVal_Bits
     (bv_or
       (bv_or
         (bv_shiftl
           (bv_zero_extend 64 (writeSuccessTransactionByte transaction 284))
           (BV 64 24))
         (bv_shiftl
           (bv_zero_extend 64 (writeSuccessTransactionByte transaction 283))
           (BV 64 16)))
       (bv_or
         (bv_shiftl
           (bv_zero_extend 64 (writeSuccessTransactionByte transaction 282))
           (BV 64 8))
         (bv_zero_extend 64 (writeSuccessTransactionByte transaction 281)))) ∗
   "x15" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 128) ∗
   "x16" ↦ᵣ RVal_Bits
     (writeSuccessTransactions15078Upper transaction) ∗
   "x17" ↦ᵣ RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64 (writeSuccessTransactionByte transaction 276))
         (BV 64 24))
       (bv_shiftl
         (bv_zero_extend 64 (writeSuccessTransactionByte transaction 275))
         (BV 64 16))) ∗
   "x18" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 48) ∗
   "x19" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 224) ∗
   "x20" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 56) ∗
   "x21" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 72) ∗
   "x22" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 200) ∗
   "x23" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 24) ∗
   "x24" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 8) ∗
   "x25" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 0) ∗
   "x26" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 184) ∗
   "x27" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32)) ∗
   "x28" ↦ᵣ RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64 (writeSuccessTransactionByte transaction 270))
         (BV 64 8))
       (bv_zero_extend 64 (writeSuccessTransactionByte transaction 269))) ∗
   "x29" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 64) ∗
   "x30" ↦ᵣ RVal_Bits
     (bv_shiftl
       (bv_zero_extend 64 (writeSuccessTransactionByte transaction 271))
       (BV 64 16)) ∗
   "x31" ↦ᵣ RVal_Bits
     (bv_shiftl
       (bv_zero_extend 64 (writeSuccessTransactionByte transaction 278))
       (BV 64 8)) ∗
   writeSuccessTransactions150b4CarrierScratch
     sp base (length transactions) (length processed) transaction
     first second third fourth items ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine150b4Carrier) := I.

Definition writeSuccessTransactionsAt150b4CarrierSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec)
      (first second third fourth : bv 64) (items : list ByteListItem),
    writeSuccessTransactionsMachine150b4Carrier
      sp base transactions processed transaction
      first second third fourth items ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      writeSuccessTransactionBytes transaction ∗
    writeSuccessTransactionsCurrentPhaseCarrierFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items ∗
    writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt150b4CarrierSpec) := I.
