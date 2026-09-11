Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15620.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15644.

Import ListNotations.

Definition writeSuccessTransactions1565cOtherRegisters : list string :=
  ["x1"; "x3"; "x4"; "x5"; "x6"; "x7";
   "x10"; "x11"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17"; "x19";
   "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x27";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessTransactions1565cOtherRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessTransactions1565cOtherRegisters.

Definition writeSuccessTransactionsMachine1565c `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  (∃ pointer : bv 64,
   reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactions1565cOtherRegShapes ∗
   "x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗
   "x9" ↦ᵣ RVal_Bits pointer ∗
   "x18" ↦ᵣ RVal_Bits (BV 64 0) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   writeSuccessTransactionsScratch15620
     sp base transactions processed transaction ∗
   ⌜bv_unsigned pointer =
     (bv_unsigned (writeSuccessTransactionWord transaction 240) +
      144 * Z.of_nat
        (length (writeSuccessTransactionAuthorizations transaction)))%Z⌝ ∗
   True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine1565c) := I.

Definition writeSuccessTransactionsAt1565cSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionPhaseHandoff TransactionTail
      (writeSuccessTransactionsMachine1565c
        sp base transactions processed transaction)
      sp base transaction transactions processed remaining
      bytes prefix suffix tail P)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt1565cSpec) := I.
