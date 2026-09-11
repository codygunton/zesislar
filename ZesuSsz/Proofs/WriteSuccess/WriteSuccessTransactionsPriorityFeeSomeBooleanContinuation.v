Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeNoneBoundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeSomeBoundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeSomeEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeSomeBooleanCallRet.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeSomeBooleanReturn.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanReturn.

Definition writeSuccessTransactionsPriorityFeeSomeBooleanFramedCallRet
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  zesu_c_call_ret 16
    (writeSuccessTransactionsPriorityFeeSavedValues transaction)
    (BV 64 0x15128) sp
    (fun args =>
      writeSuccessTransactionsPriorityFeeSomeBooleanMmio args ∗
      writeSuccessTransactionsPriorityFeeSomeBooleanTrace
        sp transaction remaining tail args ∗
      writeSuccessTransactionsPriorityFeeCallerFrame P sp base transaction
        transactions processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsPriorityFeeSomeBooleanFramedCallRet) := I.

Lemma write_success_transactions_priority_fee_some_boolean_continuation
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_body 0x15128
    (writeSuccessTransactionsPriorityFeeSomeAt15128Spec P) -∗
  instr_pre 0x15128
    (writeSuccessTransactionsPriorityFeeSomeBooleanFramedCallRet P sp base
      transaction transactions processed remaining bytes prefix suffix tail).
Proof.
  iIntros "Hnext".
  iApply (instr_pre_wand 0x15128 0x15128 false true with "Hnext");
    [done | reflexivity |].
  iIntros "Hpost".
  rewrite /writeSuccessTransactionsPriorityFeeSomeBooleanFramedCallRet.
  rewrite /writeSuccessTransactionsPriorityFeeSomeBooleanMmio
    /writeSuccessTransactionsPriorityFeeSomeBooleanTrace.
  iApply (write_success_transactions_priority_fee_some_boolean_return P sp
    base transaction transactions processed remaining bytes prefix suffix tail
    with "Hpost").
Qed.
