Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanReturn.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanCallRet.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeCore.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeNoneBoundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Definition writeSuccessTransactionsPriorityFeeBooleanFramedCallRet
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  zesu_c_call_ret 16
    (writeSuccessTransactionsPriorityFeeSavedValues transaction)
    (BV 64 0x15148) sp
    (fun args =>
      writeSuccessTransactionsPriorityFeeBooleanMmio
        sp transaction remaining tail args ∗
      writeSuccessTransactionsPriorityFeeBooleanTrace
        sp transaction remaining tail args ∗
      writeSuccessTransactionsPriorityFeeCallerFrame P sp base transaction
        transactions processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsPriorityFeeBooleanFramedCallRet) := I.

Lemma write_success_transactions_priority_fee_boolean_continuation
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_body 0x15148 (writeSuccessTransactionsPriorityFeePostSpec P) -∗
  instr_pre 0x15148
    (writeSuccessTransactionsPriorityFeeBooleanFramedCallRet P sp base
      transaction transactions processed remaining bytes prefix suffix tail).
Proof.
  iStartProof. iIntros "Hnext".
  iApply (instr_pre_wand 0x15148 0x15148 false true with "Hnext");
    [done | reflexivity |].
  iIntros "Hpost".
  rewrite /writeSuccessTransactionsPriorityFeeBooleanFramedCallRet
    /writeSuccessTransactionsPriorityFeeBooleanMmio
    /writeSuccessTransactionsPriorityFeeBooleanTrace.
  iApply (write_success_transactions_priority_fee_boolean_return P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    with "Hpost").
Qed.
