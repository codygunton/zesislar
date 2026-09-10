From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsAccessListsAdapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsAccessArrayNonzero.

Import ListNotations.

Lemma write_success_transactions_access_entry_own_nonzero
    `{!islaG Sigma} `{!threadG} (transaction : writeSuccessTransaction)
    (entry : writeSuccessAccessEntry) (entries : list writeSuccessAccessEntry)
    (HentriesCase : writeSuccessTransactionAccessEntries transaction =
      entry :: entries) :
  writeSuccessTransactionOwn transaction -∗
  bv_unsigned (writeSuccessTransactionWord transaction 208) ↦ₘ∗
    ([] : list (bv 8)) ∗
  bv_unsigned (writeSuccessTransactionWord transaction 208) ↦ₘ∗
    writeSuccessAccessEntriesBytes (entry :: entries) ∗
  writeSuccessAccessEntriesOwn (entry :: entries) ∗
  (bv_unsigned (writeSuccessTransactionWord transaction 208) ↦ₘ∗
      writeSuccessAccessEntriesBytes (entry :: entries) -∗
   writeSuccessAccessEntriesOwn (entry :: entries) -∗
   writeSuccessTransactionOwn transaction) ∗
  ⌜length (writeSuccessAccessEntriesBytes (entry :: entries)) =
    (40 * length (entry :: entries))%nat⌝ ∗
  ⌜(length (entry :: entries) < 2 ^ 64)%nat⌝ ∗
  ⌜0x20000000 <=
    bv_unsigned (writeSuccessTransactionWord transaction 208)⌝ ∗
  ⌜bv_unsigned (writeSuccessTransactionWord transaction 208) +
    Z.of_nat (length (writeSuccessAccessEntriesBytes (entry :: entries))) <
    0x40000000⌝ ∗
  ⌜writeSuccessTransactionWord transaction 208 =
    Z_to_bv 64
      (bv_unsigned (writeSuccessTransactionWord transaction 208))⌝ ∗
  ⌜writeSuccessTransactionWord transaction 216 =
    Z_to_bv 64 (Z.of_nat (length (entry :: entries)))⌝ ∗
  ⌜writeSuccessTransactionAccessBytes transaction =
    writeSuccessAccessEntriesBytes (entry :: entries)⌝.
Proof.
  iIntros "Htransaction".
  iDestruct "Htransaction" as
    "(Hdata & Haccess & Hentries & Hblob & Hauth & %Hvalid & _)".
  have Hpointer : writeSuccessTransactionWord transaction 208 =
      writeSuccessTransactionAccessPointer transaction.
  { unfold writeSuccessTransactionValid in Hvalid. naive_solver. }
  have Hcount : bv_unsigned (writeSuccessTransactionWord transaction 216) =
      Z.of_nat (length (writeSuccessTransactionAccessEntries transaction)).
  { unfold writeSuccessTransactionValid in Hvalid. naive_solver. }
  have HaccessBytes : writeSuccessTransactionAccessBytes transaction =
      writeSuccessAccessEntriesBytes
        (writeSuccessTransactionAccessEntries transaction).
  { unfold writeSuccessTransactionValid in Hvalid. naive_solver. }
  have HbaseWord : writeSuccessTransactionWord transaction 208 =
      Z_to_bv 64 (bv_unsigned (writeSuccessTransactionWord transaction 208)).
  { bv_solve. }
  have HcountWord : writeSuccessTransactionWord transaction 216 =
      Z_to_bv 64 (Z.of_nat (length (entry :: entries))).
  { have Hrange := bv_unsigned_in_range 64
      (writeSuccessTransactionWord transaction 216).
    rewrite Hcount HentriesCase in Hrange.
    unfold bv_modulus in Hrange. cbn in Hrange.
    apply bv_eq. rewrite Z_to_bv_unsigned.
    rewrite (bv_wrap_small 64 _ Hrange).
    rewrite Hcount HentriesCase. reflexivity. }
  have HentriesBound : (length (entry :: entries) < 2 ^ 64)%nat.
  { have Hrange := bv_unsigned_in_range 64
      (writeSuccessTransactionWord transaction 216).
    rewrite Hcount HentriesCase in Hrange.
    unfold bv_modulus in Hrange. cbn in Hrange.
    apply (proj2 (Nat2Z.inj_lt _ _)). rewrite Nat2Z.inj_pow.
    exact (proj2 Hrange). }
  iPoseProof (write_success_transactions_access_entries_length
    (writeSuccessTransactionAccessEntries transaction) with "Hentries")
    as "(%HaccessLength & Hentries)".
  rewrite HentriesCase in HaccessLength.
  have HbytesNonempty :
      writeSuccessAccessEntriesBytes (entry :: entries) <> [].
  { intros Hnil. rewrite Hnil in HaccessLength. cbn in HaccessLength. lia. }
  iEval (rewrite <- Hpointer; rewrite HaccessBytes HentriesCase) in "Haccess".
  iEval (rewrite HentriesCase) in "Hentries".
  iPoseProof (write_success_transactions_access_array_nonzero
    (writeSuccessTransactionWord transaction 208)
    (writeSuccessAccessEntriesBytes (entry :: entries)) HbytesNonempty
    with "Haccess") as
    "(Hempty & Harray & %HaccessLow & %HaccessHigh)".
  iSplitL "Hempty"; [iExact "Hempty"|].
  iSplitL "Harray"; [iExact "Harray"|].
  iSplitL "Hentries"; [iExact "Hentries"|].
  iSplitL "Hdata Hblob Hauth".
  { iIntros "Harray Hentries".
    iPoseProof (write_success_transactions_access_array_restore_nonzero
      (writeSuccessTransactionWord transaction 208)
      (writeSuccessAccessEntriesBytes (entry :: entries)) HbytesNonempty
      HaccessLow HaccessHigh with "Harray") as "Haccess".
    rewrite /writeSuccessTransactionOwn.
    rewrite <- Hpointer. rewrite HaccessBytes HentriesCase.
    iFrame "Hdata Haccess Hentries Hblob Hauth".
    iSplit; [iPureIntro; exact Hvalid|done]. }
  iSplit; [iPureIntro; exact HaccessLength|].
  iSplit; [iPureIntro; exact HentriesBound|].
  iSplit; [iPureIntro; exact HaccessLow|].
  iSplit; [iPureIntro; exact HaccessHigh|].
  iSplit; [iPureIntro; exact HbaseWord|].
  iSplit; [iPureIntro; exact HcountWord|].
  iPureIntro. rewrite <- HentriesCase. exact HaccessBytes.
Qed.
