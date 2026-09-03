From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14fc8.

Definition writeSuccessTransactions14fe0LoadFrame
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z)
    (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
    iProp Sigma :=
  (reg_col writeSuccessTransactions14fc8OtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits
     (bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
         transaction 272)) ∗
   "x6" ↦ᵣ RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 278))
         (BV 64 8))
       (bv_zero_extend 64
         (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
           transaction 277))) ∗
   "x8" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 192) ∗
   "x9" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 16) ∗
   "x11" ↦ᵣ RVal_Bits
     (bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
         transaction 264)) ∗
   "x12" ↦ᵣ RVal_Bits
     (bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
         transaction 265)) ∗
   "x13" ↦ᵣ RVal_Bits
     (bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
         transaction 280)) ∗
   "x14" ↦ᵣ RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 282))
         (BV 64 8))
       (bv_zero_extend 64
         (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
           transaction 281))) ∗
   "x15" ↦ᵣ RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 284))
         (BV 64 24))
       (bv_shiftl
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 283))
         (BV 64 16))) ∗
   "x16" ↦ᵣ RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 274))
         (BV 64 8))
       (bv_zero_extend 64
         (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
           transaction 273))) ∗
   "x17" ↦ᵣ RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 276))
         (BV 64 24))
       (bv_shiftl
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 275))
         (BV 64 16))) ∗
   "x18" ↦ᵣ RVal_Bits
     (bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
         transaction 279)) ∗
   "x19" ↦ᵣ RVal_Bits
     (bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
         transaction 266)) ∗
   "x20" ↦ᵣ RVal_Bits
     (bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
         transaction 267)) ∗
   "x23" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 24) ∗
   "x24" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 8) ∗
   "x25" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 0) ∗
   "x26" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 184) ∗
   "x31" ↦ᵣ RVal_Bits
     (bv_shiftl
       (bv_zero_extend 64
         (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
           transaction 278))
       (BV 64 8)) ∗
   writeSuccessTransactionsScratch14fc8
     sp base transactions processed transaction ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactions14fe0LoadFrame) := I.

Definition writeSuccessTransactionsAt14fe0LoadSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (x7 x28 x29 x30 : bv 64) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x10" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
    "x7" ↦ᵣ RVal_Bits x7 ∗
    "x28" ↦ᵣ RVal_Bits x28 ∗
    "x29" ↦ᵣ RVal_Bits x29 ∗
    "x30" ↦ᵣ RVal_Bits x30 ∗
    writeSuccessTransactions14fe0LoadFrame
      sp base transactions processed transaction ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
    writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt14fe0LoadSpec) := I.

Definition writeSuccessTransactionsAt14fe4Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ transaction,
    writeSuccessTransactionsAt14fe0LoadSpec P
      transaction
      (bv_zero_extend 64
        (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
          transaction 268))
      (bv_shiftl
        (bv_zero_extend 64
          (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 275))
        (BV 64 16))
      (bv_shiftl
        (bv_zero_extend 64
          (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 276))
        (BV 64 24))
      (bv_zero_extend 64
        (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
          transaction 277)))%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt14fe4Spec) := I.
