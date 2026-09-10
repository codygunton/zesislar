Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeNoneBoundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeSomeBoundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeSomeBooleanCallRet.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeSomeBooleanContinuation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeSomeBooleanFrameRemove.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeSomeEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanReturn.

Lemma write_success_transactions_priority_fee_some_boolean_return_pre
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_body 0x15128
    (writeSuccessTransactionsPriorityFeeSomeAt15128Spec P) -∗
  writeSuccessTransactionsPriorityFeeCallerFrame P sp base transaction
    transactions processed remaining bytes prefix suffix tail -∗
  instr_pre 0x15128
    (writeSuccessTransactionsPriorityFeeSomeBooleanCallRet
      sp transaction remaining tail).
Proof.
  iIntros "Hnext Hframe".
  iPoseProof
    (write_success_transactions_priority_fee_some_boolean_continuation P sp
      base transaction transactions processed remaining bytes prefix suffix
      tail with "Hnext") as "Hret".
  iApply (write_success_transactions_priority_fee_some_boolean_frame_remove P
    sp base transaction transactions processed remaining bytes prefix suffix
    tail
    with "Hret Hframe").
Qed.
