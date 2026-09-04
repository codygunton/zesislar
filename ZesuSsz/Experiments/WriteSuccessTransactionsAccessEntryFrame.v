From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsAccessListsAdapter.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsAccessEntryFrameZero.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsAccessEntryFrameNonzero.

Lemma write_success_transactions_access_entry_frame
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) :
  writeSuccessTransactionOwn transaction -∗
  writeSuccessTransactionsInvariant sp base transactions processed
    (transaction :: remaining) bytes prefix suffix -∗
  writeSuccessTransactionsAccessEntryResources sp base transaction
    transactions processed remaining bytes prefix suffix.
Proof.
  iIntros "Htransaction Hinvariant".
  destruct (writeSuccessTransactionAccessEntries transaction) as [|entry entries]
    eqn:HentriesCase.
  - iApply (write_success_transactions_access_entry_frame_zero
      sp base transaction transactions processed remaining bytes prefix suffix
      HentriesCase with "Htransaction Hinvariant").
  - iApply (write_success_transactions_access_entry_frame_nonzero
      sp base transaction transactions processed remaining bytes prefix suffix
      entry entries HentriesCase with "Htransaction Hinvariant").
Qed.
