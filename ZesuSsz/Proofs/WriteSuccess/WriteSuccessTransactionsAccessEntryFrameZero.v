Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsAccessListsAdapter.

Import ListNotations.

Lemma write_success_transactions_access_entry_frame_zero
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8))
    (HentriesCase : writeSuccessTransactionAccessEntries transaction = []) :
  writeSuccessTransactionOwn transaction -∗
  writeSuccessTransactionsInvariant sp base transactions processed
    (transaction :: remaining) bytes prefix suffix -∗
  writeSuccessTransactionsAccessEntryResources sp base transaction
    transactions processed remaining bytes prefix suffix.
Proof.
  iIntros "Htransaction Hinvariant".
  rewrite /writeSuccessTransactionsAccessEntryResources.
  iDestruct "Htransaction" as
    "(Hdata & Haccess & Hentries & Hblob & Hauth & %Hvalid & _)".
  iEval (rewrite /writeSuccessTransactionsInvariant) in "Hinvariant".
  iDestruct "Hinvariant" as
    "(HtransactionsEq & HbytesEq & HprefixEq & HsuffixEq & HbytesAppend &
      HbytesLength & HprefixLength & HsuffixLength & HtransactionsBound &
      %HspAlign & %HspLow & %HspHigh & HbaseAlign & HbaseLow & HbaseHigh & _)".
  have Hpointer : writeSuccessTransactionWord transaction 208 =
      writeSuccessTransactionAccessPointer transaction.
  { unfold writeSuccessTransactionValid in Hvalid. naive_solver. }
  have Hcount : bv_unsigned (writeSuccessTransactionWord transaction 216) = 0.
  { have HcountAll : bv_unsigned (writeSuccessTransactionWord transaction 216) =
        Z.of_nat (length (writeSuccessTransactionAccessEntries transaction)).
    { unfold writeSuccessTransactionValid in Hvalid. naive_solver. }
    rewrite HentriesCase in HcountAll. exact HcountAll. }
  have HaccessBytes : writeSuccessTransactionAccessBytes transaction = [].
  { have HaccessBytesAll : writeSuccessTransactionAccessBytes transaction =
        writeSuccessAccessEntriesBytes
          (writeSuccessTransactionAccessEntries transaction).
    { unfold writeSuccessTransactionValid in Hvalid. naive_solver. }
    rewrite HentriesCase in HaccessBytesAll. exact HaccessBytesAll. }
  have HbaseWord : writeSuccessTransactionWord transaction 208 =
      Z_to_bv 64 (bv_unsigned (writeSuccessTransactionWord transaction 208)).
  { bv_solve. }
  have HcountWord : writeSuccessTransactionWord transaction 216 = Z_to_bv 64 0.
  { apply bv_eq. rewrite Z_to_bv_unsigned.
    rewrite (bv_wrap_small 64 0); [exact Hcount | unfold bv_modulus; cbn; lia]. }
  iAssert (writeSuccessTransactionsInvariant sp base transactions processed
      (transaction :: remaining) bytes prefix suffix)%I
    with "[HtransactionsEq HbytesEq HprefixEq HsuffixEq HbytesAppend
      HbytesLength HprefixLength HsuffixLength HtransactionsBound HbaseAlign
      HbaseLow HbaseHigh]" as "Hinvariant".
  { rewrite /writeSuccessTransactionsInvariant.
    iFrame "HtransactionsEq HbytesEq HprefixEq HsuffixEq HbytesAppend
      HbytesLength HprefixLength HsuffixLength HtransactionsBound HbaseAlign
      HbaseLow HbaseHigh".
    repeat iSplit; try iPureIntro; try assumption; done. }
  iEval (rewrite <- Hpointer; rewrite HaccessBytes) in "Haccess".
  iEval (rewrite /writeSuccessByteArrayOwn) in "Haccess".
  have Hrange := bv_unsigned_in_range 64
    (writeSuccessTransactionWord transaction 208).
  unfold bv_modulus in Hrange. cbn in Hrange.
  iAssert (bv_unsigned (writeSuccessTransactionWord transaction 208) ↦ₘ∗
    ([] : list (bv 8)))%I with "[]" as "Hempty1".
  { iApply write_success_transactions_access_empty_array. iPureIntro; lia. }
  iAssert (bv_unsigned (writeSuccessTransactionWord transaction 208) ↦ₘ∗
    ([] : list (bv 8)))%I with "[]" as "Hempty2".
  { iApply write_success_transactions_access_empty_array. iPureIntro; lia. }
  iAssert (writeSuccessAccessListsInvariant sp
    (bv_unsigned (writeSuccessTransactionWord transaction 208)) [] [] []
    [] [] [])%I with "[]" as "HaccessInvariant".
  { rewrite /writeSuccessAccessListsInvariant.
    iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
    iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
    iSplit; [iPureIntro; cbn; lia|].
    iSplit; [iPureIntro; exact HspAlign|].
    iSplit; [iPureIntro; lia|].
    iSplit; [iPureIntro; exact HspHigh|].
    iSplit; [iPureIntro; intros Hneq; contradiction|].
    iSplit; [iPureIntro; intros Hneq; contradiction|]. done. }
  rewrite HentriesCase /=.
  iSplitL "Hempty1"; [iExact "Hempty1"|].
  iSplitL "Hempty2"; [iExact "Hempty2"|].
  iSplitL "Hentries"; [done|].
  iSplitL "Hdata Hblob Hauth".
  { iIntros "_ Hentries". rewrite /writeSuccessTransactionOwn.
    iFrame "Hdata Hblob Hauth".
    rewrite <- Hpointer. rewrite HaccessBytes /writeSuccessByteArrayOwn.
    rewrite HentriesCase /=.
    iSplit; [done|]. iSplit; [done|].
    iSplit; [iPureIntro; exact Hvalid|done]. }
  iFrame "HaccessInvariant Hinvariant".
  repeat iSplit; iPureIntro; assumption.
Qed.
