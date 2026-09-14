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
 WriteSuccessExactTransactionsSourceAuthorizationZeroSpec WriteSuccessExactAuthorizationsInitialZero.

From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsAuthorizationZeroCompleteCode
  WriteSuccessExactTransactionsSourceAuthorizationZeroCaller
  WriteSuccessExactTransactionsSourceAuthorizationZeroExit.

Lemma transactions_source_authorization_zero_continuation `{!islaG Sigma} `{!threadG}
    sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes
    tail (Q : iProp Sigma) :
  (bv_unsigned sp + 1896 < machineRamEnd defaultMap)%Z ->
  transactionRowWord bytes index 248 = BV 64 0 ->
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15620 (transactionSourceAuthorizationExit sp base bytes processed index
    dataBytes accessBytes chainBytes entries blobBytes [] tail Q) -∗
  □ instr_pre 0x15584 (authorizationCountPost sp (transactionRowWord bytes index 248) tail
    (maxBlobFeeCountFrame sp (transactionRowWord bytes index 80) (transactionRowWord bytes index 88)
      (transactionSourceBlobFeeRetained sp base bytes processed index dataBytes accessBytes
        chainBytes entries blobBytes (writeSuccessByteArrayOwn (transactionRowWord bytes index 240) [] ∗ Q)%I))).
Proof.
  intros HstackHigh Hcount.
  iStartProof. iIntros "#Hcode #Hexit".
  iAssert (□ instr_pre 0x15620 (authorizationZeroPost sp (transactionRowWord bytes index 240) tail
    (transactionSourceAuthorizationZeroFrame sp base bytes processed index dataBytes accessBytes
      chainBytes entries blobBytes Q)))%I as "#HzeroExit".
  { iModIntro. iEval (rewrite instr_pre'_eq) in "Hexit".
    iEval (rewrite instr_pre'_eq). iNext. iIntros "Hpost".
    iPoseProof (transactions_source_authorization_zero_exit with "Hpost") as "Hsource".
    iApply ("Hexit" with "Hsource"). }
  iPoseProof (transactions_authorization_zero_complete_code sp (transactionRowWord bytes index 240) tail
    (transactionSourceAuthorizationZeroFrame sp base bytes processed index dataBytes accessBytes
      chainBytes entries blobBytes Q) with "Hcode") as "#Hbody".
  iModIntro. iEval (rewrite instr_pre'_eq). iNext. iIntros "Hpost".
  iPoseProof (transactions_source_authorization_zero_caller sp base bytes processed index
    dataBytes accessBytes chainBytes entries blobBytes tail Q HstackHigh Hcount
    with "Hpost HzeroExit") as "Hentry".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply ("Hbody" with "Hentry").
Qed.
Print Assumptions transactions_source_authorization_zero_continuation.
