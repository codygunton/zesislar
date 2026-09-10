Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15620.

Import ListNotations.

Definition writeSuccessTransactions1562cOtherRegisters : list string :=
  ["x3"; "x4"; "x6"; "x7";
   "x12"; "x13"; "x14"; "x15"; "x16"; "x17"; "x19";
   "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x27";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessTransactions1562cOtherRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessTransactions1562cOtherRegisters.

Definition writeSuccessTransactionsMachine1562c `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  (∃ pointer : bv 64,
   reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactions1562cOtherRegShapes ∗
   "x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗
   "x9" ↦ᵣ RVal_Bits pointer ∗
   "x18" ↦ᵣ RVal_Bits (BV 64 0) ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x1562c) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
   writeSuccessTransactionsScratch15620
     sp base transactions processed transaction ∗
   ⌜bv_unsigned pointer =
     (bv_unsigned (writeSuccessTransactionWord transaction 240) +
      144 * Z.of_nat
        (length (writeSuccessTransactionAuthorizations transaction)))%Z⌝ ∗
   True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine1562c) := I.

Definition writeSuccessTransactionsAt1562cSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionPhaseHandoff TransactionR
      (writeSuccessTransactionsMachine1562c
        sp base transactions processed transaction)
      sp base transaction transactions processed remaining
      bytes prefix suffix tail P)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt1562cSpec) := I.
