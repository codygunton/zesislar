Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsLayout
  WriteSuccessExactTransactionsSourceFieldLayout
  WriteSuccessExactAccessListsValidity WriteSuccessExactAccessListsBytes.

Definition transactionFieldNestedOwn `{!islaG Sigma}
    (transaction : writeSuccessTransaction) : iProp Sigma :=
  (writeSuccessByteArrayOwn (writeSuccessTransactionBlobPointer transaction)
     (writeSuccessTransactionBlobBytes transaction) ∗
   writeSuccessByteArrayOwn (writeSuccessTransactionAuthorizationPointer transaction)
     (writeSuccessTransactionAuthorizationBytes transaction) ∗
   ⌜writeSuccessTransactionValid transaction⌝ ∗ True)%I.
Global Instance : LithiumUnfold (@transactionFieldNestedOwn) := I.

Lemma transactions_current_field_heap `{!islaG Sigma} processed transaction rest :
  Forall writeSuccessTransactionValid processed ->
  writeSuccessTransactionOwn transaction -∗
  transactionFieldSourceHeap
    (writeSuccessTransactionsBytes (processed ++ transaction :: rest)) (288 * length processed)
    (writeSuccessTransactionData transaction) (writeSuccessTransactionAccessBytes transaction)
    (writeSuccessTransactionAccessEntries transaction) ∗ transactionFieldNestedOwn transaction ∗ True.
Proof.
  intros Hprocessed. iStartProof. iIntros "Hown".
  iEval (unfold writeSuccessTransactionOwn) in "Hown".
  iDestruct "Hown" as "(Hdata & Haccess & Hentries & Hblob & Hauth & %Hvalid & _)".
  have HvalidCopy := Hvalid.
  destruct HvalidCopy as (Hlength & Htype & Hchain & Hnonce & Hgas & Hfee & Hlimit & Hto &
    Hvalue & HdataPointer & HdataLength & HaccessPointer & HaccessCount & HaccessBytes & Hrest).
  iDestruct (access_entries_validity with "Hentries") as "[%HentriesValid Hentries]".
  have HaccessLength : length (writeSuccessTransactionAccessBytes transaction) =
      (40 * length (writeSuccessTransactionAccessEntries transaction))%nat.
  { rewrite HaccessBytes. exact (access_entries_bytes_length _ HentriesValid). }
  have Hcount : writeSuccessTransactionWord transaction 216 =
      Z_to_bv 64 (Z.of_nat (length (writeSuccessTransactionAccessEntries transaction))).
  { rewrite -HaccessCount Z_to_bv_bv_unsigned. reflexivity. }
  have Hbound : (length (writeSuccessTransactionAccessEntries transaction) < 2 ^ 64)%nat.
  { apply Nat2Z.inj_lt. rewrite Nat2Z.inj_pow.
    change (Z.of_nat (length (writeSuccessTransactionAccessEntries transaction)) < 2 ^ 64)%Z.
    rewrite -HaccessCount. exact (proj2 (bv_unsigned_in_range 64 (writeSuccessTransactionWord transaction 216))). }
  rewrite /transactionFieldSourceHeap /transactionFieldNestedOwn
    (exact_transaction_row_word processed transaction rest 192 Hprocessed Hvalid ltac:(lia))
    (exact_transaction_row_word processed transaction rest 208 Hprocessed Hvalid ltac:(lia))
    (exact_transaction_row_word processed transaction rest 200 Hprocessed Hvalid ltac:(lia))
    (exact_transaction_row_word processed transaction rest 216 Hprocessed Hvalid ltac:(lia))
    HdataPointer HaccessPointer Hcount.
  iFrame. repeat iSplit; try done. all: iPureIntro; tauto.
Qed.
Print Assumptions transactions_current_field_heap.
