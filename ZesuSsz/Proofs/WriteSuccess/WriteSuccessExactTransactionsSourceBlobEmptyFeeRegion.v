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
  WriteSuccessExactTransactionsSourceFieldEvents WriteSuccessExactAccessListsReturnCount
  WriteSuccessExactEncoderIntFramedCall WriteSuccessExactAccessListsRegisterGroups.

From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsSourceBlobEmptyFeeEntry
  WriteSuccessExactTransactionsFeeCountCompleteCode.

Lemma transactions_source_blob_empty_fee_region_correct `{!islaG Sigma} `{!threadG}
    sp base bytes processed index dataBytes accessBytes chainBytes entries tail
    (Q : iProp Sigma) :
  transactionRowWord bytes index 232 = BV 64 0 ->
  (mapRamBase defaultMap) <= bv_unsigned sp - 32 ->
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15584 (authorizationCountPost sp (transactionRowWord bytes index 248) tail
    (maxBlobFeeCountFrame sp (transactionRowWord bytes index 80) (transactionRowWord bytes index 88)
      (transactionSourceBlobFeeRetained sp base bytes processed index dataBytes accessBytes
        chainBytes entries [] Q))) -∗
  instr_body 0x15564 (transactionSourceFieldPost sp base bytes processed index dataBytes accessBytes chainBytes entries
    (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
      (writeSuccessU128WordsPayload (transactionRowWord bytes index 80) (transactionRowWord bytes index 88))
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64
          (bv_unsigned (transactionRowWord bytes index 248)))) tail))
    (writeSuccessByteArrayOwn (transactionRowWord bytes index 224) [] ∗ Q)%I).
Proof.
  intros Hzero Hlower.
  iStartProof. iIntros "#Hcode #Hnext".
  iEval (rewrite instr_pre'_eq). iIntros "Hentry".
  iDestruct (transactions_source_blob_empty_fee_entry sp base bytes processed index
    dataBytes accessBytes chainBytes entries tail Q Hzero Hlower
    with "Hentry Hnext") as (oldra old5) "Hentry".
  iPoseProof (transactions_fee_count_complete_code sp (transactionRowWord bytes index 80)
    (transactionRowWord bytes index 88) (transactionRowWord bytes index 248)
    oldra old5 tail
    (transactionSourceBlobFeeRetained sp base bytes processed index dataBytes accessBytes
      chainBytes entries [] Q) with "Hcode") as "Hfee".
  iEval (rewrite instr_pre'_eq) in "Hfee".
  iApply ("Hfee" with "Hentry").
Qed.
Print Assumptions transactions_source_blob_empty_fee_region_correct.
