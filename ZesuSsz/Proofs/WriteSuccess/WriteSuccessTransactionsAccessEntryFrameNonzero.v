Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsAccessListsAdapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsAccessEntryInvariant.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsAccessTransactionInvariant.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsAccessEntryOwnNonzero.

Import ListNotations.

Lemma write_success_transactions_access_entry_frame_nonzero
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8))
    (entry : writeSuccessAccessEntry) (entries : list writeSuccessAccessEntry)
    (HentriesCase : writeSuccessTransactionAccessEntries transaction =
      entry :: entries) :
  writeSuccessTransactionOwn transaction -∗
  writeSuccessTransactionsInvariant sp base transactions processed
    (transaction :: remaining) bytes prefix suffix -∗
  writeSuccessTransactionsAccessEntryResources sp base transaction
    transactions processed remaining bytes prefix suffix.
Proof.
  iIntros "Htransaction Hinvariant".
  iPoseProof (write_success_transactions_access_transaction_invariant
    sp base transactions processed (transaction :: remaining)
    bytes prefix suffix with "Hinvariant")
    as "(%HspAlign & %HspLow & %HspHigh & Hinvariant)".
  iPoseProof (write_success_transactions_access_entry_own_nonzero
    transaction entry entries HentriesCase with "Htransaction")
    as "(Hempty & Harray & Hentries & Hrestore & %Hlength & %Hbound &
      %HbaseLow & %HbaseHigh & %HbaseWord & %HcountWord & %HaccessBytes)".
  iPoseProof (write_success_transactions_access_entry_invariant sp
    (bv_unsigned (writeSuccessTransactionWord transaction 208))
    (entry :: entries) (writeSuccessAccessEntriesBytes (entry :: entries))
    ltac:(discriminate) eq_refl Hlength Hbound HspAlign HspLow HspHigh
    HbaseLow HbaseHigh) as "HaccessInvariant".
  rewrite /writeSuccessTransactionsAccessEntryResources HentriesCase.
  iFrame "Hempty Harray Hentries Hrestore HaccessInvariant Hinvariant".
  iSplit; [iPureIntro; exact HbaseWord|].
  iSplit; [iPureIntro; exact HcountWord|].
  iPureIntro. exact HaccessBytes.
Qed.
