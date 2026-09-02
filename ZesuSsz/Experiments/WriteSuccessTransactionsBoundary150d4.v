From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15028.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15088.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary1508c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15090.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15094.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15098.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary1509c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150a0.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150a4.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150a8.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150ac.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150b0.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150b4.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150b8.

Import ListNotations.

Definition writeSuccessTransactions150d4OtherRegisters : list string :=
  ["x1"; "x3"; "x4"].

Definition writeSuccessTransactions150d4OtherRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessTransactions150d4OtherRegisters.

Definition writeSuccessTransactionsScratch150d4 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ
     Z_to_bv 64 (Z.of_nat (length transactions)) ∗
   (bv_unsigned sp + 120) ↦ₘ
     bv_zero_extend 64 (writeSuccessTransactionByte transaction 285) ∗
   (bv_unsigned sp + 128) ↦ₘ writeSuccessTransactionWord transaction 64 ∗
   (bv_unsigned sp + 136) ↦ₘ
     writeSuccessTransactionWord transaction 232 ∗
   (bv_unsigned sp + 144) ↦ₘ writeSuccessTransactionWord transaction 88 ∗
   (bv_unsigned sp + 152) ↦ₘ writeSuccessTransactionWord transaction 80 ∗
   (bv_unsigned sp + 160) ↦ₘ
     writeSuccessTransactionWord transaction 248 ∗
   (bv_unsigned sp + 168) ↦ₘ
     writeSuccessTransactionWord transaction 240 ∗
   (bv_unsigned sp + 176) ↦ₘ
     writeSuccessTransactionWord transaction 256 ∗
   (bv_unsigned sp + 184) ↦ₘ
     writeSuccessTransactionWord transaction 120 ∗
   (bv_unsigned sp + 192) ↦ₘ writeSuccessTransactionWord transaction 112 ∗
   (bv_unsigned sp + 200) ↦ₘ writeSuccessTransactionWord transaction 104 ∗
   (bv_unsigned sp + 208) ↦ₘ
     writeSuccessTransactionWord transaction 128 ∗
   (bv_unsigned sp + 216) ↦ₘ writeSuccessTransactionWord transaction 96 ∗
   (bv_unsigned sp + 224) ↦ₘ writeSuccessTransactionWord transaction 152 ∗
   (bv_unsigned sp + 232) ↦ₘ writeSuccessTransactionWord transaction 144 ∗
   (bv_unsigned sp + 240) ↦ₘ writeSuccessTransactionWord transaction 136 ∗
   (bv_unsigned sp + 248) ↦ₘ
     Z_to_bv 64 (Z.of_nat (length processed)) ∗
   (bv_unsigned sp + 256) ↦ₘ
     writeSuccessTransactionWord transaction 208 ∗
   (bv_unsigned sp + 264) ↦ₘ
     writeSuccessTransactionWord transaction 216 ∗
   (bv_unsigned sp + 272) ↦ₘ writeSuccessTransactionWord transaction 176 ∗
   (bv_unsigned sp + 280) ↦ₘ? 1360 ∗
   (bv_unsigned sp + 1640) ↦ₘ
     writeSuccessTransactionWord transaction 265 ∗
   (bv_unsigned sp + 1648) ↦ₘ? 16 ∗
   (bv_unsigned sp + 1664) ↦ₘ writeSuccessTransactionWord transaction 160 ∗
   (bv_unsigned sp + 1672) ↦ₘ writeSuccessTransactionWord transaction 168 ∗
   (bv_unsigned sp + 1680) ↦ₘ? 216 ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsScratch150d4) := I.

Definition writeSuccessTransactionsMachine150d4 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactions150d4OtherRegShapes ∗
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
     (writeSuccessTransactionWord transaction 256) ∗
   "x11" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 264)) ∗
   "x12" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 248) ∗
   "x13" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 273) ∗
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
   "x16" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 265) ∗
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
   writeSuccessTransactionsScratch150d4
     sp base transactions processed transaction ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine150d4) := I.

Definition writeSuccessTransactionsAt150d4Spec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionsMachine150d4
      sp base transactions processed transaction ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      writeSuccessTransactionBytes transaction ∗
    writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt150d4Spec) := I.
