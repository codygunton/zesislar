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

Lemma transactions_source_authorization_zero_caller `{!islaG Sigma} `{!threadG}
    sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes
    tail (Q : iProp Sigma) :
  (bv_unsigned sp + 1896 < machineRamEnd defaultMap)%Z ->
  transactionRowWord bytes index 248 = BV 64 0 ->
  authorizationCountPost sp (transactionRowWord bytes index 248) tail
    (maxBlobFeeCountFrame sp (transactionRowWord bytes index 80) (transactionRowWord bytes index 88)
      (transactionSourceBlobFeeRetained sp base bytes processed index dataBytes accessBytes
        chainBytes entries blobBytes (writeSuccessByteArrayOwn (transactionRowWord bytes index 240) [] ∗ Q)%I)) -∗
  instr_pre 0x15620 (authorizationZeroPost sp (transactionRowWord bytes index 240) tail
    (transactionSourceAuthorizationZeroFrame sp base bytes processed index dataBytes accessBytes
      chainBytes entries blobBytes Q)) -∗
  authorizationZeroEntry sp (transactionRowWord bytes index 240) tail
    (transactionSourceAuthorizationZeroFrame sp base bytes processed index dataBytes accessBytes
      chainBytes entries blobBytes Q).
Proof.
  intros HstackHigh Hcount.
  iIntros "Hpost Hnext".
  iEval (unfold authorizationCountPost, encoderIntExactFramedPost) in "Hpost".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hupper & Hmmio & Htrace & Hcountframe & _)".
  iDestruct "Hcountframe" as "(Hcountword & H18 & %Halign & %Hlow & %Hhigh & Hfeeframe & _)".
  iDestruct "Hfeeframe" as "(Hmiddle & Hfeehigh & Hfeelow & %Hfeealign & %Hfeelowbound & %Hfeehighbound & Hretained & _)".
  iPoseProof (transactions_source_authorization_memory_frame sp base bytes processed index
    dataBytes accessBytes chainBytes entries blobBytes [] Q HstackHigh
    with "Hretained") as "[Hborrowed Hloan]".
  iEval (rewrite Hcount) in "H18".
  iEval (unfold transactionSourceAuthorizationBorrowed, writeSuccessByteArrayOwn) in "Hborrowed".
  unfold authorizationZeroEntry, transactionSourceAuthorizationZeroFrame.
  zesu_open_resource_groups; zesu_open_bits_registers; zesu_run.
Qed.
Print Assumptions transactions_source_authorization_zero_caller.
