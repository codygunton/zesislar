Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15028.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15048.

Definition writeSuccessTransactionsMachine15048WithX16AndScratch
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (x16 : bv 64) (scratch : iProp Sigma) :
    iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col (delete 3%nat writeSuccessTransactions15028OtherRegShapes) ∗
   "x21" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 72) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 272))
         (BV 64 24))
       (bv_shiftl
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 271))
         (BV 64 16))) ∗
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
   "x7" ↦ᵣ RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 268))
         (BV 64 24))
       (bv_shiftl
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 267))
         (BV 64 16))) ∗
   "x8" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 192) ∗
   "x9" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 16) ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
   "x11" ↦ᵣ RVal_Bits
     (bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
         transaction 264)) ∗
   "x12" ↦ᵣ RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 266))
         (BV 64 8))
       (bv_zero_extend 64
         (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
           transaction 265))) ∗
   "x13" ↦ᵣ RVal_Bits
     (bv_or
       (bv_or
         (bv_shiftl
           (bv_zero_extend 64
             (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
               transaction 280))
           (BV 64 24))
         (bv_shiftl
           (bv_zero_extend 64
             (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
               transaction 279))
           (BV 64 16)))
       (bv_or
         (bv_shiftl
           (bv_zero_extend 64
             (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
               transaction 278))
           (BV 64 8))
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 277)))) ∗
   "x14" ↦ᵣ RVal_Bits
     (bv_or
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
           (BV 64 16)))
       (bv_or
         (bv_shiftl
           (bv_zero_extend 64
             (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
               transaction 282))
           (BV 64 8))
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 281)))) ∗
   "x15" ↦ᵣ RVal_Bits
     (bv_or
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
           (BV 64 16)))
       (bv_or
         (bv_shiftl
           (bv_zero_extend 64
             (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
               transaction 274))
           (BV 64 8))
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 273)))) ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗
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
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 48) ∗
   "x19" ↦ᵣ RVal_Bits
     (bv_shiftl
       (bv_zero_extend 64
         (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
           transaction 266))
       (BV 64 8)) ∗
   "x20" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 56) ∗
   "x23" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 24) ∗
   "x24" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 8) ∗
   "x25" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 0) ∗
   "x26" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 184) ∗
   "x27" ↦ᵣ RVal_Bits
     (bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
         transaction 32)) ∗
   "x28" ↦ᵣ RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 270))
         (BV 64 8))
       (bv_zero_extend 64
         (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
           transaction 269))) ∗
   "x29" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 64) ∗
   "x30" ↦ᵣ RVal_Bits
     (bv_shiftl
       (bv_zero_extend 64
         (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
           transaction 271))
       (BV 64 16)) ∗
   "x31" ↦ᵣ RVal_Bits
     (bv_shiftl
       (bv_zero_extend 64
         (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
           transaction 278))
       (BV 64 8)) ∗
   scratch ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsMachine15048WithX16AndScratch) := I.

Definition writeSuccessTransactionsScratch1505c `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
    iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ
     Z_to_bv 64 (Z.of_nat (length transactions)) ∗
   (bv_unsigned sp + 120) ↦ₘ
     bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
         transaction 285) ∗
   (bv_unsigned sp + 128) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 64 ∗
   (bv_unsigned sp + 136) ↦ₘ? 8 ∗
   (bv_unsigned sp + 144) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 88 ∗
   (bv_unsigned sp + 152) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 80 ∗
   (bv_unsigned sp + 160) ↦ₘ? 64 ∗
   (bv_unsigned sp + 224) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 152 ∗
   (bv_unsigned sp + 232) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 144 ∗
   (bv_unsigned sp + 240) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 136 ∗
   (bv_unsigned sp + 248) ↦ₘ
     Z_to_bv 64 (Z.of_nat (length processed)) ∗
   (bv_unsigned sp + 256) ↦ₘ? 16 ∗
   (bv_unsigned sp + 272) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 176 ∗
   (bv_unsigned sp + 280) ↦ₘ? 1384 ∗
   (bv_unsigned sp + 1664) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 160 ∗
   (bv_unsigned sp + 1672) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 168 ∗
   (bv_unsigned sp + 1680) ↦ₘ? 216 ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsScratch1505c) := I.

Definition writeSuccessTransactionsMachine1505c `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
    iProp Sigma :=
  writeSuccessTransactionsMachine15048WithX16AndScratch
    sp base transactions processed transaction
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
      transaction 96)
    (writeSuccessTransactionsScratch1505c
      sp base transactions processed transaction).

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine1505c) := I.

Definition writeSuccessTransactionsAt1505cSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionsMachine1505c
      sp base transactions processed transaction ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
    writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt1505cSpec) := I.
