From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15154.

Import ListNotations.

(** The state at [0x15168], after the three source loads. *)
Definition writeSuccessTransactions15168OtherRegisters : list string :=
  ["x3"; "x4"; "x6"; "x7";
   "x13"; "x14"; "x15"; "x16"; "x17";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessTransactions15168OtherRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessTransactions15168OtherRegisters.

Definition writeSuccessTransactionsMachine15168 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactions15168OtherRegShapes ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15154) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   "x8" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 192) ∗
   "x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 16) ∗
   "x10" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 265) ∗
   "x11" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 273) ∗
   "x12" ↦ᵣ RVal_Bits
     (bv_sign_extend 64
       (bv_extract 0 32
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
             (bv_zero_extend 64 (writeSuccessTransactionByte transaction 281)))))) ∗
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
   writeSuccessTransactionsScratch150e8
     sp base transactions processed transaction ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine15168) := I.

Definition writeSuccessTransactionsOptionalAddressSomeAt15168Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    ⌜writeSuccessTransactionByte transaction 285 ≠ BV 8 0⌝ ∗
    writeSuccessTransactionPhaseHandoff TransactionTo
      (writeSuccessTransactionsMachine15168
        sp base transactions processed transaction)
      sp base transaction transactions processed remaining
      bytes prefix suffix tail P)%I.

Global Instance :
  LithiumUnfold (@writeSuccessTransactionsOptionalAddressSomeAt15168Spec) := I.

(** The stack state after [sd x10, 1744(sp)] at [0x15168]. *)
Definition writeSuccessTransactionsScratch1516Prefix `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat (length transactions)) ∗
   (bv_unsigned sp + 120) ↦ₘ
     bv_zero_extend 64 (writeSuccessTransactionByte transaction 285) ∗
   (bv_unsigned sp + 128) ↦ₘ writeSuccessTransactionWord transaction 64 ∗
   (bv_unsigned sp + 136) ↦ₘ writeSuccessTransactionWord transaction 232 ∗
   (bv_unsigned sp + 144) ↦ₘ writeSuccessTransactionWord transaction 88 ∗
   (bv_unsigned sp + 152) ↦ₘ writeSuccessTransactionWord transaction 80 ∗
   (bv_unsigned sp + 160) ↦ₘ writeSuccessTransactionWord transaction 248 ∗
   (bv_unsigned sp + 168) ↦ₘ writeSuccessTransactionWord transaction 240 ∗
   (bv_unsigned sp + 176) ↦ₘ writeSuccessTransactionWord transaction 256 ∗
   (bv_unsigned sp + 184) ↦ₘ writeSuccessTransactionWord transaction 120 ∗
   (bv_unsigned sp + 192) ↦ₘ writeSuccessTransactionWord transaction 112 ∗
   (bv_unsigned sp + 200) ↦ₘ writeSuccessTransactionWord transaction 104 ∗
   (bv_unsigned sp + 208) ↦ₘ writeSuccessTransactionWord transaction 128 ∗
   (bv_unsigned sp + 216) ↦ₘ writeSuccessTransactionWord transaction 96 ∗
   (bv_unsigned sp + 224) ↦ₘ writeSuccessTransactionWord transaction 152 ∗
   (bv_unsigned sp + 232) ↦ₘ writeSuccessTransactionWord transaction 144 ∗
   (bv_unsigned sp + 240) ↦ₘ writeSuccessTransactionWord transaction 136 ∗
   (bv_unsigned sp + 248) ↦ₘ Z_to_bv 64 (Z.of_nat (length processed)) ∗
   (bv_unsigned sp + 256) ↦ₘ writeSuccessTransactionWord transaction 208 ∗
   (bv_unsigned sp + 264) ↦ₘ writeSuccessTransactionWord transaction 216 ∗
   (bv_unsigned sp + 272) ↦ₘ writeSuccessTransactionWord transaction 176 ∗
   (bv_unsigned sp + 280) ↦ₘ? 1360 ∗
   (bv_unsigned sp + 1640) ↦ₘ writeSuccessTransactionWord transaction 265 ∗
   (bv_unsigned sp + 1648) ↦ₘ writeSuccessTransactionWord transaction 273 ∗
   (bv_unsigned sp + 1656) ↦ₘ
     bv_extract 0 32
       (bv_or
         (bv_or
           (bv_shiftl (bv_zero_extend 64
             (writeSuccessTransactionByte transaction 284)) (BV 64 24))
           (bv_shiftl (bv_zero_extend 64
             (writeSuccessTransactionByte transaction 283)) (BV 64 16)))
         (bv_or
           (bv_shiftl (bv_zero_extend 64
             (writeSuccessTransactionByte transaction 282)) (BV 64 8))
           (bv_zero_extend 64 (writeSuccessTransactionByte transaction 281)))) ∗
   (bv_unsigned sp + 1660) ↦ₘ? 4 ∗
   (bv_unsigned sp + 1664) ↦ₘ writeSuccessTransactionWord transaction 160 ∗
   (bv_unsigned sp + 1672) ↦ₘ writeSuccessTransactionWord transaction 168 ∗
   (bv_unsigned sp + 1680) ↦ₘ? 64 ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsScratch1516Prefix) := I.

Definition writeSuccessTransactionsScratch1516c `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  (writeSuccessTransactionsScratch1516Prefix sp base transactions processed transaction ∗
   (bv_unsigned sp + 1744) ↦ₘ writeSuccessTransactionWord transaction 265 ∗
   (bv_unsigned sp + 1752) ↦ₘ? 144 ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsScratch1516c) := I.

Definition writeSuccessTransactions1516cRegisters `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactions15168OtherRegShapes ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15154) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   "x8" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 192) ∗
   "x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 16) ∗
   "x10" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 265) ∗
   "x11" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 273) ∗
   "x12" ↦ᵣ RVal_Bits
     (bv_sign_extend 64
       (bv_extract 0 32
         (bv_or
           (bv_or
             (bv_shiftl (bv_zero_extend 64
               (writeSuccessTransactionByte transaction 284)) (BV 64 24))
             (bv_shiftl (bv_zero_extend 64
               (writeSuccessTransactionByte transaction 283)) (BV 64 16)))
           (bv_or
             (bv_shiftl (bv_zero_extend 64
               (writeSuccessTransactionByte transaction 282)) (BV 64 8))
             (bv_zero_extend 64
               (writeSuccessTransactionByte transaction 281)))))) ∗
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
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32)) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactions1516cRegisters) := I.

Definition writeSuccessTransactionsMachine1516c `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  (writeSuccessTransactions1516cRegisters sp base transactions processed transaction ∗
   writeSuccessTransactionsScratch1516c
     sp base transactions processed transaction ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine1516c) := I.

Definition writeSuccessTransactionsOptionalAddressSomeAt1516cSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    ⌜writeSuccessTransactionByte transaction 285 ≠ BV 8 0⌝ ∗
    writeSuccessTransactionPhaseHandoff TransactionTo
      (writeSuccessTransactionsMachine1516c
        sp base transactions processed transaction)
      sp base transaction transactions processed remaining
      bytes prefix suffix tail P)%I.

Global Instance :
  LithiumUnfold (@writeSuccessTransactionsOptionalAddressSomeAt1516cSpec) := I.

(** The state after [sd x11, 1752(sp)] at [0x1516c]. *)
Definition writeSuccessTransactionsScratch15170 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  (writeSuccessTransactionsScratch1516Prefix sp base transactions processed transaction ∗
   (bv_unsigned sp + 1744) ↦ₘ writeSuccessTransactionWord transaction 265 ∗
   (bv_unsigned sp + 1752) ↦ₘ writeSuccessTransactionWord transaction 273 ∗
   (bv_unsigned sp + 1760) ↦ₘ? 136 ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsScratch15170) := I.

Definition writeSuccessTransactionsMachine15170 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  (writeSuccessTransactions1516cRegisters sp base transactions processed transaction ∗
   writeSuccessTransactionsScratch15170 sp base transactions processed transaction ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine15170) := I.

Definition writeSuccessTransactionsOptionalAddressSomeAt15170Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    ⌜writeSuccessTransactionByte transaction 285 ≠ BV 8 0⌝ ∗
    writeSuccessTransactionPhaseHandoff TransactionTo
      (writeSuccessTransactionsMachine15170 sp base transactions processed transaction)
      sp base transaction transactions processed remaining bytes prefix suffix tail P)%I.

Global Instance :
  LithiumUnfold (@writeSuccessTransactionsOptionalAddressSomeAt15170Spec) := I.
