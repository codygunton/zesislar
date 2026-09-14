Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsLiveSpec
  WriteSuccessExactTransactionsLiveBlobFrame.

Definition transactionLiveAuthorizationRemainder `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed : list writeSuccessTransaction)
    (transaction : writeSuccessTransaction) (rest : list writeSuccessTransaction)
    (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat (length transactions)) ∗
   writeSuccessTransactionsOwn processed ∗ writeSuccessTransactionsOwn rest ∗
   ⌜writeSuccessTransactionValid transaction⌝ ∗
   ⌜transactionLoopSourceFacts sp base transactions processed (transaction :: rest) bytes⌝ ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionLiveAuthorizationRemainder) := I.

Lemma transactions_live_authorization_frame `{!islaG Sigma} `{!threadG}
    sp base transactions processed transaction rest bytes (P : iProp Sigma) :
  transactionLiveAuthorizationFrame sp base transactions processed transaction rest bytes P ⊣⊢
  writeSuccessByteArrayOwn (writeSuccessTransactionAuthorizationPointer transaction)
    (writeSuccessTransactionAuthorizationBytes transaction) ∗
  transactionLiveAuthorizationRemainder sp base transactions processed transaction rest bytes P.
Proof.
  iStartProof. iSplit.
  - iIntros "(Htotal & Hprocessed & Hrest & Hauth & %Hvalid & %Hfacts & HP & _)".
    iSplitL "Hauth"; first iExact "Hauth".
    unfold transactionLiveAuthorizationRemainder.
    iSplitL "Htotal"; first iExact "Htotal".
    iSplitL "Hprocessed"; first iExact "Hprocessed".
    iSplitL "Hrest"; first iExact "Hrest".
    iSplit; first done. iSplit; first done.
    iSplitL "HP"; [iExact "HP" | done].
  - iIntros "(Hauth & Htotal & Hprocessed & Hrest & %Hvalid & %Hfacts & HP & _)".
    unfold transactionLiveAuthorizationFrame.
    iSplitL "Htotal"; first iExact "Htotal".
    iSplitL "Hprocessed"; first iExact "Hprocessed".
    iSplitL "Hrest"; first iExact "Hrest".
    iSplitL "Hauth"; first iExact "Hauth".
    iSplit; first done. iSplit; first done.
    iSplitL "HP"; [iExact "HP" | done].
Qed.
Print Assumptions transactions_live_authorization_frame.
