From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15564.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15574.

Import ListNotations.

Definition writeSuccessTransactions15584OtherRegisters : list string :=
  ["x3"; "x4"; "x6"; "x7"; "x8"; "x9";
   "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x20"; "x21"; "x23"; "x24"; "x25"; "x26"; "x27";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessTransactions15584OtherRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessTransactions15584OtherRegisters.

Definition writeSuccessTransactionsMachine15584 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  (∃ pointer : bv 64,
   reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactions15584OtherRegShapes ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15584) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
   "x18" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 248) ∗
   "x19" ↦ᵣ RVal_Bits pointer ∗
   "x22" ↦ᵣ RVal_Bits (BV 64 0) ∗
   writeSuccessTransactionsScratch15564
     sp base transactions processed transaction ∗
   ⌜bv_unsigned pointer =
     (bv_unsigned (writeSuccessTransactionWord transaction 224) +
      32 * Z.of_nat
        (length (writeSuccessTransactionBlobHashes transaction)))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine15584) := I.

Definition writeSuccessTransactionsAt15584Spec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionPhaseHandoff TransactionAuthorizations
      (writeSuccessTransactionsMachine15584
        sp base transactions processed transaction)
      sp base transaction transactions processed remaining
      bytes prefix suffix tail P)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15584Spec) := I.
