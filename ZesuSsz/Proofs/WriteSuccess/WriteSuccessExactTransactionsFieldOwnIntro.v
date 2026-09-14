Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsFieldHeap
  WriteSuccessExactTransactionsSourceFieldLayout WriteSuccessExactTransactionsLayout.

Lemma transactions_current_field_own `{!islaG Sigma} prefix transaction rest :
  Forall writeSuccessTransactionValid prefix ->
  transactionFieldSourceHeap
    (writeSuccessTransactionsBytes (prefix ++ transaction :: rest)) (288 * length prefix)
    (writeSuccessTransactionData transaction) (writeSuccessTransactionAccessBytes transaction)
    (writeSuccessTransactionAccessEntries transaction) -∗
  transactionFieldNestedOwn transaction -∗ writeSuccessTransactionOwn transaction.
Proof.
  intros Hprefix. iStartProof. iIntros "Hheap Hnested".
  iDestruct "Hnested" as "(Hblob & Hauth & %Hvalid & _)".
  iDestruct "Hheap" as "(Hdata & Haccess & Hentries & _)".
  have Hcopy := Hvalid.
  destruct Hcopy as (Hlength & Htype & Hchain & Hnonce & Hgas & Hfee & Hlimit & Hto &
    Hvalue & HdataPointer & HdataLength & HaccessPointer & Hrest).
  have Hdata := exact_transaction_row_word prefix transaction rest 192 Hprefix Hvalid ltac:(lia).
  have Haccess := exact_transaction_row_word prefix transaction rest 208 Hprefix Hvalid ltac:(lia).
  rewrite HdataPointer in Hdata. rewrite HaccessPointer in Haccess.
  unfold writeSuccessTransactionOwn.
  rewrite -Hdata -Haccess.
  iSplitL "Hdata"; first iExact "Hdata".
  iSplitL "Haccess"; first iExact "Haccess".
  iSplitL "Hentries"; first iExact "Hentries".
  iSplitL "Hblob"; first iExact "Hblob".
  iSplitL "Hauth"; first iExact "Hauth".
  done.
Qed.
Print Assumptions transactions_current_field_own.
