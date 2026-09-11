Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15564.

Import ListNotations.

Definition writeSuccessTransactions15574OtherRegisters : list string :=
  ["x3"; "x4"; "x6"; "x7"; "x8"; "x9";
   "x12"; "x13"; "x14"; "x15"; "x16"; "x17"; "x18";
   "x20"; "x21"; "x23"; "x24"; "x25"; "x26"; "x27";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessTransactions15574OtherRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessTransactions15574OtherRegisters.

Definition writeSuccessTransactionsMachine15574 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  (∃ pointer : bv 64,
   reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactions15574OtherRegShapes ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15574) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 32)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 16) ∗
   "x19" ↦ᵣ RVal_Bits pointer ∗
   "x22" ↦ᵣ RVal_Bits (BV 64 0) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
   writeSuccessTransactionsScratch15564
     sp base transactions processed transaction ∗
   ⌜bv_unsigned pointer =
     (bv_unsigned (writeSuccessTransactionWord transaction 224) +
      32 * Z.of_nat
        (length (writeSuccessTransactionBlobHashes transaction)))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine15574) := I.

Definition writeSuccessTransactionsAt15574Spec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionPhaseHandoff TransactionAuthorizationCount
      (writeSuccessTransactionsMachine15574
        sp base transactions processed transaction)
      sp base transaction transactions processed remaining
      bytes prefix suffix tail P)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15574Spec) := I.
