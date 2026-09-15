Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessTransactionsSpec
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsLiveFieldFrame
  WriteSuccessExactTransactionsLiveBlobFrame
  WriteSuccessExactTransactionsSourceAuthorizationLiveFrame
  WriteSuccessExactTransactionsSourceBlobFeeChain
  WriteSuccessExactTransactionsSourceBlobFeeFrame
  WriteSuccessExactAuthorizationsCount WriteSuccessExactTransactionsMaxBlobFeeCount
  WriteSuccessExactTransactionsSourceFieldEvents
  WriteSuccessExactTransactionsLiveCompositionFrames
  WriteSuccessExactBlobHashesModel
  WriteSuccessExactEncoderU128 WriteSuccessObservation WriteSuccessOutputSemantic.

Lemma transactions_live_blob_field_guard `{!islaG Sigma} `{!threadG}
    sp base transactions processed transaction rest bytes
    dataBytes accessBytes chainBytes entries blobBytes authBytes
    authorizationTail expectedTail (P : iProp Sigma) :
  blobBytes = writeSuccessTransactionBlobBytes transaction ->
  authBytes = writeSuccessTransactionAuthorizationBytes transaction ->
  length blobBytes =
    (32 * length (writeSuccessTransactionBlobHashes transaction))%nat ->
  transactionRowWord bytes (288 * length processed) 232 =
    Z_to_bv 64 (Z.of_nat (length (writeSuccessTransactionBlobHashes transaction))) ->
  (Z.of_nat (length (writeSuccessTransactionBlobHashes transaction)) <
    18446744073709551616)%Z ->
  transactionRowWord bytes (288 * length processed) 224 =
    writeSuccessTransactionBlobPointer transaction ->
  transactionRowWord bytes (288 * length processed) 240 =
    writeSuccessTransactionAuthorizationPointer transaction ->
  (mapRamBase defaultMap <= bv_unsigned sp - 32)%Z ->
  writeSuccessExactBlobHashesEvents sp 0
    (length (writeSuccessTransactionBlobHashes transaction)) blobBytes
    (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
      (writeSuccessU128WordsPayload
        (transactionRowWord bytes (288 * length processed) 80)
        (transactionRowWord bytes (288 * length processed) 88))
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64
          (bv_unsigned (transactionRowWord bytes (288 * length processed) 248))))
        authorizationTail)) = expectedTail ->
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15584
    (authorizationCountPost sp
      (transactionRowWord bytes (288 * length processed) 248) authorizationTail
      (maxBlobFeeCountFrame sp
        (transactionRowWord bytes (288 * length processed) 80)
        (transactionRowWord bytes (288 * length processed) 88)
        (transactionSourceBlobFeeRetained sp base bytes (length processed)
          (288 * length processed) dataBytes accessBytes chainBytes entries blobBytes
          (writeSuccessByteArrayOwn
             (transactionRowWord bytes (288 * length processed) 240) authBytes ∗
           transactionLiveAuthorizationRemainder sp base transactions processed
             transaction rest bytes P)%I))) -∗
  □ instr_pre 0x153d0
    (transactionSourceFieldPost sp base bytes (length processed)
      (288 * length processed) dataBytes accessBytes chainBytes entries expectedTail
      (transactionLiveFieldFrame sp base transactions processed transaction rest bytes P)).
Proof.
  intros HblobBytes HauthBytes HblobLength HblobCount HblobBound HblobPointer
    HauthPointer HstackLow Hevents.
  iIntros "#Hcode #Hcount".
  iModIntro. iApply instr_pre_to_body. iNext.
  iPoseProof (transactions_source_blob_fee_chain_correct sp base bytes
    (length processed) (288 * length processed) dataBytes accessBytes chainBytes
    entries blobBytes (length (writeSuccessTransactionBlobHashes transaction))
    authorizationTail
    (writeSuccessByteArrayOwn
       (transactionRowWord bytes (288 * length processed) 240) authBytes ∗
     transactionLiveAuthorizationRemainder sp base transactions processed
       transaction rest bytes P)%I
    HblobLength HblobCount HblobBound HstackLow
    with "Hcode Hcount") as "Hchain".
  iApply (instr_pre_wand with "Hchain"); [done | done |].
  iIntros "Hpost". iEval (rewrite Hevents).
  iApply (transaction_source_field_post_mono with "[] Hpost").
  iIntros "Hframe". rewrite HblobPointer HauthPointer.
  iDestruct (transactions_live_blob_frame sp base transactions processed
    transaction rest bytes P with "Hframe") as "(Hblob & HauthFrame)".
  iDestruct (transactions_live_authorization_frame sp base transactions processed
    transaction rest bytes P with "HauthFrame") as "(Hauth & Hremainder)".
  rewrite HblobBytes HauthBytes.
  iFrame.
Qed.
Print Assumptions transactions_live_blob_field_guard.
