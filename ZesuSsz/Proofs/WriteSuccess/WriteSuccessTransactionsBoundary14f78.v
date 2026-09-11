Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundarySpec.

Import ListNotations.

Definition writeSuccessTransactions14f78OtherRegisters : list string :=
  ["x1"; "x3"; "x4"; "x7"; "x18"; "x19"; "x20"; "x21"; "x22";
   "x27"; "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessTransactions14f78OtherRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64)) <$>
    writeSuccessTransactions14f78OtherRegisters.

Definition writeSuccessTransactionsMachine14f78
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z)
    (transactions processed : list writeSuccessTransaction)
    (transaction : writeSuccessTransaction) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactions14f78OtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 272)) ∗
   "x6" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 273)) ∗
   "x8" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 192) ∗
   "x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 16) ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
   "x11" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 160) ∗
   "x12" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 168) ∗
   "x13" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 280)) ∗
   "x14" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 281)) ∗
   "x15" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 282)) ∗
   "x16" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 283)) ∗
   "x17" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 284)) ∗
   "x23" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 24) ∗
   "x24" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 8) ∗
   "x25" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 0) ∗
   "x26" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 184) ∗
   writeSuccessTransactionsScratch14f68
     sp base transactions processed transaction ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine14f78) := I.

Definition writeSuccessTransactionsAt14f78Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionsMachine14f78
      sp base transactions processed transaction ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      writeSuccessTransactionBytes transaction ∗
    writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt14f78Spec) := I.
