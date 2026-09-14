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

Lemma transactions_source_blob_empty_fee_entry `{!islaG Sigma} `{!threadG}
    sp base bytes processed index dataBytes accessBytes chainBytes entries tail
    (Q : iProp Sigma) :
  transactionRowWord bytes index 232 = BV 64 0 ->
  (mapRamBase defaultMap) <= bv_unsigned sp - 32 ->
  transactionSourceFieldPost sp base bytes processed index dataBytes accessBytes chainBytes entries
    (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
      (writeSuccessU128WordsPayload (transactionRowWord bytes index 80) (transactionRowWord bytes index 88))
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64
          (bv_unsigned (transactionRowWord bytes index 248)))) tail))
    (writeSuccessByteArrayOwn (transactionRowWord bytes index 224) [] ∗ Q)%I -∗
  instr_pre 0x15584 (authorizationCountPost sp (transactionRowWord bytes index 248) tail
    (maxBlobFeeCountFrame sp (transactionRowWord bytes index 80) (transactionRowWord bytes index 88)
      (transactionSourceBlobFeeRetained sp base bytes processed index dataBytes accessBytes
        chainBytes entries [] Q))) -∗
  ∃ oldra old5 : bv 64,
    authorizationPrefixEntry sp (transactionRowWord bytes index 80) (transactionRowWord bytes index 88)
      (transactionRowWord bytes index 248) oldra old5 tail
      (transactionSourceBlobFeeRetained sp base bytes processed index dataBytes accessBytes
        chainBytes entries [] Q).
Proof.
  intros Hzero Hlower.
  iStartProof. iIntros "Hpost Hnext".
  iEval (unfold transactionSourceFieldPost, accessReturnCountPost, encoderIntExactFramedPost,
    accessReturnCountFrame, accessReturnLoopFrame, accessReturnRuntimeBounds,
    transactionAccessRetainedMemory) in "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hlower & Hmmio & Htrace & (H22 & Hsaved & Hloop & _) & _)".
  iDestruct "Hloop" as (storedIndex old27)
    "(Htmp & Hother & H19 & H27 & Haccess & Hown & HaccessBase & HaccessCount & HaccessIndex &
      Hcopied & Hkeys & (%Halign & %Hlow & %Hhigh &
      (Hsrc0 & Hsrc1 & Hsrc2 & Htag & Hvalue & Hdata & Hlower32 &
       (Hchain & Hmemory & _) & _) & _) & _)".
  iEval (rewrite Hzero) in "H22".
  iPoseProof (transactions_source_fee_frame with "Hmemory") as
    "(HfeeHigh & HfeeLow & Hcount & Hmemory)".
  iEval (unfold accessRegisterGroup) in "Htmp Hother".
  iDestruct "Hkeys" as (key0 key1 key2 key3) "Hkeys".
  iEval (unfold transactionFieldSourceFeeRest, writeSuccessByteArrayOwn) in "Hmemory".
  iExists (BV 64 0x153d0), (BV 64 (mapIoContextAddress defaultMap)).
  unfold authorizationPrefixEntry, transactionSourceBlobFeeRetained, writeSuccessByteArrayOwn.
  zesu_open_resource_groups.
  zesu_run.
Qed.
Print Assumptions transactions_source_blob_empty_fee_entry.
