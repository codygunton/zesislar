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

From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactAuthorizationsCompleteCountContinuation
  WriteSuccessExactTransactionsSourceAuthorizationCountCaller
  WriteSuccessExactTransactionsSourceAuthorizationLoopExit.

Lemma transactions_source_authorization_count_continuation `{!islaG Sigma} `{!threadG}
    sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes authBytes
    row authRest tail (Q : iProp Sigma) :
  authorizationLoopFacts sp (transactionRowWord bytes index 240)
    (bv_unsigned (transactionRowWord bytes index 240)) (row :: authRest) [] row authRest authBytes ->
  transactionRowWord bytes index 248 = Z_to_bv 64 (Z.of_nat (S (length authRest))) ->
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15620 (transactionSourceAuthorizationExit sp base bytes processed index
    dataBytes accessBytes chainBytes entries blobBytes authBytes tail Q) -∗
  □ instr_pre 0x15584 (authorizationCountPost sp (transactionRowWord bytes index 248)
    (writeSuccessExactAuthorizationEvents sp (row :: authRest) tail)
    (maxBlobFeeCountFrame sp (transactionRowWord bytes index 80) (transactionRowWord bytes index 88)
      (transactionSourceBlobFeeRetained sp base bytes processed index dataBytes accessBytes
        chainBytes entries blobBytes
        (writeSuccessByteArrayOwn (transactionRowWord bytes index 240) authBytes ∗ Q)%I))).
Proof.
  intros Hfacts Hcount.
  have Hcopy := Hfacts.
  destruct Hcopy as (_ & _ & _ & _ & _ & _ & _ & _ & Hlow & Hhigh).
  iStartProof. iIntros "#Hcode #Hexit".
  iAssert (□ instr_pre 0x15620 (authorizationLoopExit sp
    (bv_unsigned (transactionRowWord bytes index 240)) authBytes tail
    (authorizationInitialFrame sp (bv_unsigned (transactionRowWord bytes index 240))
      (authorizationFeeFrame sp (transactionRowWord bytes index 80) (transactionRowWord bytes index 88)
        authRest (transactionSourceAuthorizationLoan sp base bytes processed index dataBytes accessBytes
          chainBytes entries blobBytes authBytes Q)))))%I as "#HloopExit".
  { iModIntro. iEval (rewrite instr_pre'_eq) in "Hexit".
    iEval (rewrite instr_pre'_eq). iNext. iIntros "Hpost".
    iPoseProof (transactions_source_authorization_loop_exit sp base bytes processed index
      dataBytes accessBytes chainBytes entries blobBytes authBytes authRest tail Q
      Hcount Hlow Hhigh with "Hpost") as "Hsource".
    iApply ("Hexit" with "Hsource"). }
  iPoseProof (authorization_complete_count_continuation sp
    (transactionRowWord bytes index 80) (transactionRowWord bytes index 88)
    (bv_unsigned (transactionRowWord bytes index 240)) row authRest authBytes tail
    (transactionSourceAuthorizationLoan sp base bytes processed index dataBytes accessBytes
      chainBytes entries blobBytes authBytes Q) with "Hcode") as "#HcountNative".
  iModIntro. iEval (rewrite instr_pre'_eq) in "HcountNative".
  iEval (rewrite instr_pre'_eq). iNext. iIntros "Hpost".
  iPoseProof (transactions_source_authorization_count_caller sp base bytes processed index
    dataBytes accessBytes chainBytes entries blobBytes authBytes row authRest tail Q
    Hfacts Hcount with "Hpost HloopExit") as "Hcaller".
  iApply ("HcountNative" with "Hcaller").
Qed.
Print Assumptions transactions_source_authorization_count_continuation.
