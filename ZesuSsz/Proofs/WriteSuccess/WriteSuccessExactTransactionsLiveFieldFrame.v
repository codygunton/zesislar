Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsLiveSpec
  WriteSuccessExactTransactionsLoopIndexEntry WriteSuccessExactTransactionsOwnership
  WriteSuccessExactTransactionsLayout WriteSuccessExactTransactionsFieldHeap
  WriteSuccessExactTransactionsSourceFieldLayout.

Definition transactionLiveFieldFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed : list writeSuccessTransaction)
    (transaction : writeSuccessTransaction) (rest : list writeSuccessTransaction)
    (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat (length transactions)) ∗
   writeSuccessTransactionsOwn processed ∗ writeSuccessTransactionsOwn rest ∗
   transactionFieldNestedOwn transaction ∗
   ⌜transactionLoopSourceFacts sp base transactions processed (transaction :: rest) bytes⌝ ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionLiveFieldFrame) := I.

Lemma transactions_live_field_frame `{!islaG Sigma} `{!threadG}
    sp base transactions processed transaction rest bytes (P : iProp Sigma) :
  transactionLoopSourceFrame sp base transactions processed (transaction :: rest) bytes P -∗
  (bv_unsigned sp - 48) ↦ₘ? 48 ∗
  transactionFieldSourceHeap bytes (288 * length processed)
    (writeSuccessTransactionData transaction) (writeSuccessTransactionAccessBytes transaction)
    (writeSuccessTransactionAccessEntries transaction) ∗
  transactionLiveFieldFrame sp base transactions processed transaction rest bytes P ∗ True.
Proof.
  iStartProof. iIntros "Hframe".
  iEval (unfold transactionLoopSourceFrame) in "Hframe".
  iDestruct "Hframe" as "(Hlower & Htotal & Hown & %Hfacts & HP & _)".
  have HfactsCopy := Hfacts.
  destruct HfactsCopy as (Hrelation & Hbytes & _).
  iDestruct (exact_transactions_own_valid with "Hown") as "(Hown & %Hvalid & _)".
  rewrite Hrelation in Hvalid. apply Forall_app in Hvalid as [Hprocessed Hremaining].
  iEval (rewrite Hrelation transactions_own_app) in "Hown".
  iDestruct "Hown" as "(Hprocessed & Hremaining & _)".
  iEval (cbn [writeSuccessTransactionsOwn]) in "Hremaining".
  iDestruct "Hremaining" as "(Htransaction & Hrest & _)".
  iPoseProof (transactions_current_field_heap processed transaction rest Hprocessed
    with "Htransaction") as "(Hheap & Hnested & _)".
  iEval (rewrite -Hrelation -Hbytes) in "Hheap".
  iSplitL "Hlower"; first iExact "Hlower".
  iSplitL "Hheap"; first iExact "Hheap".
  iSplitL; last done. unfold transactionLiveFieldFrame.
  iSplitL "Htotal"; first iExact "Htotal".
  iSplitL "Hprocessed"; first iExact "Hprocessed".
  iSplitL "Hrest"; first iExact "Hrest".
  iSplitL "Hnested"; first iExact "Hnested".
  iSplit; first (iPureIntro; exact Hfacts).
  iSplitL "HP"; [iExact "HP" | done].
Qed.
Print Assumptions transactions_live_field_frame.
