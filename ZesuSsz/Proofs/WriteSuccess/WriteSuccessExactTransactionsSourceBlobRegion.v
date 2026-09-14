Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessBlobHashesSpec WriteSuccessExactBlobHashesModel
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsSourceFieldEvents
  WriteSuccessNativeCode WriteSuccessExactBlobHashesCompleteEntry
  WriteSuccessExactTransactionsSourceBlobHeaderHandoff.
Lemma transactions_source_blob_region_correct `{!islaG Sigma} `{!threadG}
    sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes total tail
    (Q : iProp Sigma) :
  (0 < total)%nat ->
  length blobBytes = (32 * total)%nat ->
  transactionRowWord bytes index 232 = Z_to_bv 64 (Z.of_nat total) ->
  (Z.of_nat total < 18446744073709551616)%Z ->
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15564 (writeSuccessBlobHashesLoopExit sp
    (bv_unsigned (transactionRowWord bytes index 224)) total blobBytes tail
    (transactionSourceBlobRetained sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes Q)) -∗
  instr_body 0x153d0 (transactionSourceFieldPost sp base bytes processed index dataBytes accessBytes chainBytes entries
    (writeSuccessExactBlobHashesEvents sp 0 total blobBytes tail)
    (writeSuccessByteArrayOwn (transactionRowWord bytes index 224) blobBytes ∗ Q)%I).
Proof.
  intros Hpositive Hlength Hcount Hbound.
  iStartProof. iIntros "#Hcode #Hnext".
  iPoseProof (blob_complete_native_entry_correct sp (transactionRowWord bytes index 224)
    (bv_unsigned (transactionRowWord bytes index 224)) total blobBytes tail
    (transactionSourceBlobRetained sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes Q)
    with "Hcode") as "Hbody".
  iApply (instr_pre_wand 0x153d0 0x153d0 false false with "Hbody"); [done | done |].
  iIntros "Hpost".
  iApply (transactions_source_blob_header_handoff with "Hpost Hnext"); done.
Qed.
Print Assumptions transactions_source_blob_region_correct.
