Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.

Import ListNotations.

Definition writeSuccessTransactions151b4OtherRegisters : list string :=
  ["x1"; "x3"; "x4"; "x5"; "x6"; "x7"; "x10"; "x11";
   "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessTransactions151b4OtherRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessTransactions151b4OtherRegisters.

Definition writeSuccessTransactionsMachine151b4 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactions151b4OtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x8" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 192) ∗
   "x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 16) ∗
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
   writeSuccessTransactionsScratch1519c
     sp base transactions processed transaction ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine151b4) := I.

Definition writeSuccessTransactionsAt151b4Spec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionPhaseHandoff TransactionData
      (writeSuccessTransactionsMachine151b4
        sp base transactions processed transaction)
      sp base transaction transactions processed remaining
      bytes prefix suffix tail P)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt151b4Spec) := I.
