Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeNoneBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeSomeBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeSomeEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeSomeBooleanCallRet.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeSomeBooleanReturn.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeBooleanReturn.

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
