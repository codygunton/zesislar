Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallRetFrameRight.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanCallRet.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanContinuation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanReturn.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeNoneBoundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Lemma write_success_transactions_priority_fee_boolean_frame_remove
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_pre 0x15148
    (writeSuccessTransactionsPriorityFeeBooleanFramedCallRet P sp base
      transaction transactions processed remaining bytes prefix suffix tail) -∗
  writeSuccessTransactionsPriorityFeeCallerFrame P sp base transaction
    transactions processed remaining bytes prefix suffix tail -∗
  instr_pre 0x15148
    (writeSuccessTransactionsPriorityFeeBooleanCallRet
      sp transaction remaining tail).
Proof.
  iStartProof. iIntros "Hret Hframe".
  iEval (unfold writeSuccessTransactionsPriorityFeeBooleanFramedCallRet)
    in "Hret".
  rewrite /writeSuccessTransactionsPriorityFeeBooleanCallRet.
  iApply (write_success_call_ret_frame_right2 16
    (writeSuccessTransactionsPriorityFeeSavedValues transaction)
    (BV 64 0x15148) sp
    (writeSuccessTransactionsPriorityFeeBooleanMmio
      sp transaction remaining tail)
    (writeSuccessTransactionsPriorityFeeBooleanTrace
      sp transaction remaining tail)
    (writeSuccessTransactionsPriorityFeeCallerFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail)
    with "Hret Hframe").
Qed.
