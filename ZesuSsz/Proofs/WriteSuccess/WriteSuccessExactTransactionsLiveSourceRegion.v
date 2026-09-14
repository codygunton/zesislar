Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.NatBounds.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessTransactionsSpec WriteSuccessExactTransactionsLiveSpec
  WriteSuccessExactTransactionsSpec
  WriteSuccessExactTransactionsLoopIndexEntry WriteSuccessExactTransactionsIndexCell
  WriteSuccessExactTransactionsIndexSourceEntry WriteSuccessExactTransactionsIndexFieldFrame
  WriteSuccessExactTransactionsLiveFieldFrame WriteSuccessExactTransactionsSourceFieldLayout
  WriteSuccessExactTransactionsSourceFieldEvents WriteSuccessExactTransactionsSourceChainModel
  WriteSuccessExactTransactionsSourceChainSomeRegion WriteSuccessExactTransactionsSourceChainNoneRegion
  WriteSuccessExactTransactionsChainWordImage WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactTransactionsRowWordTag WriteSuccessExactTransactionsRowByte
  WriteSuccessExactTransactionsTypeTailModel WriteSuccessExactTransactionsBlobCountTailModel.

Lemma transactions_live_source_region_correct `{!islaG Sigma} `{!threadG}
    sp base transactions processed transaction rest bytes tail (P : iProp Sigma) :
  transactionLoopSourceFacts sp base transactions processed (transaction :: rest) bytes ->
  Forall writeSuccessTransactionValid processed ->
  writeSuccessTransactionValid transaction ->
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x153d0 (transactionSourceFieldPost sp base bytes (length processed)
    (288 * length processed) (writeSuccessTransactionData transaction)
    (writeSuccessTransactionAccessBytes transaction)
    (transactionChainWordImage (transactionRowWord bytes (288 * length processed) 160)
      (transactionRowWord bytes (288 * length processed) 168))
    (writeSuccessTransactionAccessEntries transaction)
    (writeSuccessExactTransactionAfterBlobCountEvents sp transaction
      (writeSuccessExactTransactionsEvents sp rest tail))
    (transactionLiveFieldFrame sp base transactions processed transaction rest bytes P)) -∗
  instr_body 0x14f08 (transactionIndexCellEntry sp (Z_to_bv 64 base)
    (Z_to_bv 64 (Z.of_nat (length processed)))
    (Z_to_bv 64 (Z.of_nat (length transactions)))
    (transactionIndexSourceCaller sp base bytes (length processed)
      (writeSuccessExactTransactionAfterTypeEvents sp transaction
        (writeSuccessExactTransactionsEvents sp rest tail))
      (transactionLoopSourceFrame sp base transactions processed (transaction :: rest) bytes P))).
Proof.
  intros Hfacts Hprefix Hvalid. iStartProof. iIntros "#Hcode #Hnext".
  destruct Hfacts as (Hrelation & Hbytes & Hlength & Hcount & Halign & Hlow & Hhigh & Hrest).
  zesu_normalize_nat_powers.
  have Hfull : (288 * length processed + 288 <= length bytes)%nat.
  { clear -Hlength Hrelation. rewrite Hlength Hrelation app_length /=. lia. }
  have Htag := transactions_row_word_tag bytes (288 * length processed) 168 ltac:(clear -Hfull; lia).
  rewrite Hbytes Hrelation (exact_transaction_row_byte processed transaction rest 168
    Hprefix Hvalid ltac:(lia)) in Htag.
  rewrite -Hrelation -Hbytes in Htag.
  have Hmodel := transactions_source_chain_model sp processed transaction rest
    (writeSuccessExactTransactionsEvents sp rest tail) Hprefix Hvalid.
  cbn zeta in Hmodel. rewrite -Hrelation -Hbytes in Hmodel.
  have Hchain := proj1 (proj2 (proj2 Hvalid)).
  destruct (writeSuccessTransactionChainId transaction) as [chain|] eqn:Hoption.
  - cbn in Hchain. destruct Hchain as [Hnonzero Hvalue].
    have HtagNonzero : bv_extract 0 8 (transactionRowWord bytes (288 * length processed) 168) <> BV 8 0.
    { rewrite Htag. exact Hnonzero. }
    iPoseProof (transactions_source_chain_some_region_correct sp _ base bytes (length processed)
      _ _ _ _ _ HtagNonzero Halign Hlow Hhigh with "Hcode Hnext") as "Hregion".
    iApply (instr_pre_wand 0x14f08 0x14f08 false false with "Hregion"); [done | done |].
    iIntros "Hentry". iEval (rewrite -Hmodel) in "Hentry".
    iApply (transactions_index_field_frame with "Hentry").
  - cbn in Hchain.
    have HtagZero : bv_extract 0 8 (transactionRowWord bytes (288 * length processed) 168) = BV 8 0.
    { rewrite Htag. exact Hchain. }
    iPoseProof (transactions_source_chain_none_region_correct sp _ base bytes (length processed)
      _ _ _ _ _ HtagZero Halign Hlow Hhigh with "Hcode Hnext") as "Hregion".
    iApply (instr_pre_wand 0x14f08 0x14f08 false false with "Hregion"); [done | done |].
    iIntros "Hentry". iEval (rewrite -Hmodel) in "Hentry".
    iApply (transactions_index_field_frame with "Hentry").
Qed.
Print Assumptions transactions_live_source_region_correct.
