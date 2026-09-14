Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessStorageKeysSpec WriteSuccessAccessListsSpec
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsFlagLoads
  WriteSuccessExactTransactionsSourceFieldLayout WriteSuccessExactTransactionsSourceBlobFeeFrame.

Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSourceAuthorizationSpec
  WriteSuccessExactTransactionsSourceAuthorizationMemoryLoan
  WriteSuccessExactTransactionsSourceAuthorizationInitialCaller
  WriteSuccessExactEncoderIntFramedCall
  WriteSuccessExactAuthorizationsLoopSpec WriteSuccessExactAuthorizationsInitial
  WriteSuccessExactAuthorizationsCountInitial WriteSuccessExactAuthorizationsCount
  WriteSuccessExactTransactionsMaxBlobFeeCount WriteSuccessExactAuthorizationsModel.

Lemma transactions_source_authorization_count_caller `{!islaG Sigma} `{!threadG}
    sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes authBytes
    row authRest tail (Q : iProp Sigma) :
  authorizationLoopFacts sp (transactionRowWord bytes index 240)
    (bv_unsigned (transactionRowWord bytes index 240)) (row :: authRest) [] row authRest authBytes ->
  transactionRowWord bytes index 248 = Z_to_bv 64 (Z.of_nat (S (length authRest))) ->
  authorizationCountPost sp (transactionRowWord bytes index 248)
    (writeSuccessExactAuthorizationEvents sp (row :: authRest) tail)
    (maxBlobFeeCountFrame sp (transactionRowWord bytes index 80) (transactionRowWord bytes index 88)
      (transactionSourceBlobFeeRetained sp base bytes processed index dataBytes accessBytes
        chainBytes entries blobBytes
        (writeSuccessByteArrayOwn (transactionRowWord bytes index 240) authBytes ∗ Q)%I)) -∗
  instr_pre 0x15620 (authorizationLoopExit sp (bv_unsigned (transactionRowWord bytes index 240))
    authBytes tail (authorizationInitialFrame sp (bv_unsigned (transactionRowWord bytes index 240))
      (authorizationFeeFrame sp (transactionRowWord bytes index 80) (transactionRowWord bytes index 88)
        authRest (transactionSourceAuthorizationLoan sp base bytes processed index dataBytes accessBytes
          chainBytes entries blobBytes authBytes Q)))) -∗
  authorizationCountPost sp (Z_to_bv 64 (Z.of_nat (S (length authRest))))
    (writeSuccessExactAuthorizationEvents sp (row :: authRest) tail)
    (maxBlobFeeCountFrame sp (transactionRowWord bytes index 80) (transactionRowWord bytes index 88)
      (authorizationInitialCaller sp (transactionRowWord bytes index 80) (transactionRowWord bytes index 88)
        (bv_unsigned (transactionRowWord bytes index 240)) row authRest authBytes tail
        (transactionSourceAuthorizationLoan sp base bytes processed index dataBytes accessBytes
          chainBytes entries blobBytes authBytes Q))).
Proof.
  intros Hfacts Hcount.
  have HfactsCopy := Hfacts.
  destruct HfactsCopy as (_ & _ & _ & _ & _ & _ & _ & HstackHigh & _).
  iIntros "Hpost Hnext".
  iEval (unfold authorizationCountPost, encoderIntExactFramedPost) in "Hpost".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hupper & Hmmio & Htrace & Hcountframe & _)".
  iDestruct "Hcountframe" as "(Hcountword & H18 & %Halign & %Hlow & %Hhigh & Hfeeframe & _)".
  iDestruct "Hfeeframe" as "(Hmiddle & Hfeehigh & Hfeelow & %Hfeealign & %Hfeelowbound & %Hfeehighbound & Hretained & _)".
  iPoseProof (transactions_source_authorization_memory_frame sp base bytes processed index
    dataBytes accessBytes chainBytes entries blobBytes authBytes Q HstackHigh
    with "Hretained") as "[Hborrowed Hloan]".
  iPoseProof (transactions_source_authorization_initial_caller sp (transactionRowWord bytes index 80)
    (transactionRowWord bytes index 88) bytes index row authRest authBytes tail
    (transactionSourceAuthorizationLoan sp base bytes processed index dataBytes accessBytes
      chainBytes entries blobBytes authBytes Q) Hfacts with "Hborrowed Hloan Hnext") as "Hcaller".
  iEval (rewrite Hcount) in "Hcountword H18".
  iEval (unfold authorizationInitialCaller) in "Hcaller".
  iEval (rewrite Z_to_bv_bv_unsigned) in "Hcaller".
  unfold authorizationCountPost, encoderIntExactFramedPost, authorizationCountFrame, maxBlobFeeCountFrame.
  zesu_open_resource_groups; zesu_open_bits_registers; zesu_run.
Qed.
Print Assumptions transactions_source_authorization_count_caller.
