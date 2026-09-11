Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSomeHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

(** The state after [sw x12, 1760(sp)] at [0x15170]. *)
Definition writeSuccessTransactionsScratch15174 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  (writeSuccessTransactionsScratch1516Prefix sp base transactions processed transaction ∗
   (bv_unsigned sp + 1744) ↦ₘ writeSuccessTransactionWord transaction 265 ∗
   (bv_unsigned sp + 1752) ↦ₘ writeSuccessTransactionWord transaction 273 ∗
   (bv_unsigned sp + 1760) ↦ₘ
     bv_extract 0 32
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
   (bv_unsigned sp + 1764) ↦ₘ? 132 ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsScratch15174) := I.

Definition writeSuccessTransactionsMachine15174 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  (writeSuccessTransactions1516cRegisters sp base transactions processed transaction ∗
   writeSuccessTransactionsScratch15174 sp base transactions processed transaction ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine15174) := I.

Definition writeSuccessTransactionsOptionalAddressSomeAt15174Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    ⌜writeSuccessTransactionByte transaction 285 ≠ BV 8 0⌝ ∗
    writeSuccessTransactionPhaseHandoff TransactionTo
      (writeSuccessTransactionsMachine15174 sp base transactions processed transaction)
      sp base transaction transactions processed remaining bytes prefix suffix tail P)%I.

Global Instance :
  LithiumUnfold (@writeSuccessTransactionsOptionalAddressSomeAt15174Spec) := I.
