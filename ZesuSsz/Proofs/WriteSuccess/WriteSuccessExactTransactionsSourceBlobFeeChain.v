Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.UninitWords.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsFlagLoads
  WriteSuccessExactTransactionsSourceFieldLayout
  WriteSuccessExactAccessListsReturnLoopEntry
  WriteSuccessExactTransactionsDataAccessEntry
  WriteSuccessExactBlobHashesAuthorizationEntry
  WriteSuccessTransactionsSpec WriteSuccessStorageKeysSpec WriteSuccessAccessListsSpec
  WriteSuccessBlobHashesSpec WriteSuccessExactAuthorizationsPrefix
  WriteSuccessExactAuthorizationsCount WriteSuccessExactTransactionsMaxBlobFeeCount
  WriteSuccessExactEncoderU128 WriteSuccessObservation WriteSuccessOutputSemantic.

From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSourceBlobHeaderHandoff
  WriteSuccessExactTransactionsSourceBlobFeeFrame.

From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsSourceBlobFeeEntry
  WriteSuccessExactTransactionsFeeCountCompleteCode.

From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSourceFieldEvents
  WriteSuccessExactBlobHashesModel WriteSuccessExactTransactionsSourceBlobRegion
  WriteSuccessExactTransactionsSourceBlobEmptyRegion
  WriteSuccessExactTransactionsSourceBlobFeeRegion
  WriteSuccessExactTransactionsSourceBlobEmptyFeeRegion.

Lemma transactions_source_blob_fee_chain_correct `{!islaG Sigma} `{!threadG}
    sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes total tail
    (Q : iProp Sigma) :
  length blobBytes = (32 * total)%nat ->
  transactionRowWord bytes index 232 = Z_to_bv 64 (Z.of_nat total) ->
  (Z.of_nat total < 18446744073709551616)%Z ->
  (mapRamBase defaultMap) <= bv_unsigned sp - 32 ->
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15584 (authorizationCountPost sp (transactionRowWord bytes index 248) tail
    (maxBlobFeeCountFrame sp (transactionRowWord bytes index 80) (transactionRowWord bytes index 88)
      (transactionSourceBlobFeeRetained sp base bytes processed index dataBytes accessBytes
        chainBytes entries blobBytes Q))) -∗
  instr_body 0x153d0 (transactionSourceFieldPost sp base bytes processed index
    dataBytes accessBytes chainBytes entries
    (writeSuccessExactBlobHashesEvents sp 0 total blobBytes
      (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
      (writeSuccessU128WordsPayload (transactionRowWord bytes index 80) (transactionRowWord bytes index 88))
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64
          (bv_unsigned (transactionRowWord bytes index 248)))) tail)))
    (writeSuccessByteArrayOwn (transactionRowWord bytes index 224) blobBytes ∗ Q)%I).
Proof.
  intros Hlength Hcount Hbound Hlower.
  iStartProof. iIntros "#Hcode #Hnext".
  set (feeTail := (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
      (writeSuccessU128WordsPayload (transactionRowWord bytes index 80) (transactionRowWord bytes index 88))
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64
          (bv_unsigned (transactionRowWord bytes index 248)))) tail))).
  destruct total as [|total].
  - have Hempty : blobBytes = [] by destruct blobBytes; simpl in *; [done | lia].
    subst blobBytes.
    have Hzero : transactionRowWord bytes index 232 = BV 64 0 by rewrite Hcount; bv_solve.
    cbn [writeSuccessExactBlobHashesEvents].
    iApply (transactions_source_blob_empty_correct sp base bytes processed index
      dataBytes accessBytes chainBytes entries feeTail
      (writeSuccessByteArrayOwn (transactionRowWord bytes index 224) [] ∗ Q)%I
      Hzero with "Hcode []").
    iModIntro.
    iPoseProof (transactions_source_blob_empty_fee_region_correct sp base bytes processed index
      dataBytes accessBytes chainBytes entries tail Q Hzero Hlower
      with "Hcode Hnext") as "Hfee".
    iApply (instr_pre_wand 0x15564 0x15564 false true with "Hfee"); [done | done |].
    iIntros "Hpost". iExact "Hpost".
  - have Hpositive : (0 < S total)%nat by lia.
    iApply (transactions_source_blob_region_correct sp base bytes processed index
      dataBytes accessBytes chainBytes entries blobBytes (S total) feeTail Q
      Hpositive Hlength Hcount Hbound with "Hcode []").
    iModIntro.
    iPoseProof (transactions_source_blob_fee_region_correct sp base bytes processed index
      dataBytes accessBytes chainBytes entries blobBytes (S total) tail Q
      Hpositive Hlength Hlower with "Hcode Hnext") as "Hfee".
    iApply (instr_pre_wand 0x15564 0x15564 false true with "Hfee"); [done | done |].
    iIntros "Hpost". iExact "Hpost".
Qed.
Print Assumptions transactions_source_blob_fee_chain_correct.
