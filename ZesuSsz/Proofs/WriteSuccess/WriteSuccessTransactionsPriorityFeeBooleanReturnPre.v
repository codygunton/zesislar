Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallRetFrameRight.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanCallRet.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanContinuation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanFrameRemove.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanReturn.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeCore.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeNoneBoundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Lemma write_success_transactions_priority_fee_boolean_return_pre
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_body 0x15148 (writeSuccessTransactionsPriorityFeePostSpec P) -∗
  writeSuccessTransactionsPriorityFeeCallerFrame P sp base transaction
    transactions processed remaining bytes prefix suffix tail -∗
  instr_pre 0x15148
    (writeSuccessTransactionsPriorityFeeBooleanCallRet
      sp transaction remaining tail).
Proof.
  iStartProof. iIntros "Hnext Hframe".
  iPoseProof (write_success_transactions_priority_fee_boolean_continuation P sp
    base transaction transactions processed remaining bytes prefix suffix tail
    with "Hnext") as "Hret".
  iPoseProof (write_success_transactions_priority_fee_boolean_frame_remove P sp
    base transaction transactions processed remaining bytes prefix suffix tail
    with "Hret Hframe") as "Hret".
  iExact "Hret".
Qed.
