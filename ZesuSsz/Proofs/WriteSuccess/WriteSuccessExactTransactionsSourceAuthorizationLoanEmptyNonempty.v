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
  WriteSuccessExactTransactionsSourceAuthorizationSpec.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSourceAuthorizationBorrowEmptyNonempty
  WriteSuccessExactTransactionsSourceAuthorizationRestoreEmptyNonempty.

Lemma transactions_source_authorization_memory_emptynonempty `{!islaG Sigma} `{!threadG}
    sp base bytes processed index dataBytes accessBytes chainBytes entries
    (auth : bv 8) (authBytes : list (bv 8))
    (Q : iProp Sigma) :
  (bv_unsigned sp + 1896 < machineRamEnd defaultMap)%Z ->
  transactionSourceBlobFeeRetained sp base bytes processed index dataBytes accessBytes
    chainBytes entries []
    (writeSuccessByteArrayOwn (transactionRowWord bytes index 240) (auth :: authBytes) ∗ Q)%I -∗
  transactionSourceAuthorizationBorrowed sp bytes index (auth :: authBytes) ∗
  transactionSourceAuthorizationLoan sp base bytes processed index dataBytes accessBytes
    chainBytes entries [] (auth :: authBytes) Q.
Proof.
  intros HstackHigh. iIntros "Hframe".
  iPoseProof (transactions_source_authorization_borrow_emptynonempty sp base bytes processed index
    dataBytes accessBytes chainBytes entries auth authBytes Q HstackHigh
    with "Hframe") as "[Hborrowed Hremaining]".
  iSplitL "Hborrowed"; first iExact "Hborrowed".
  unfold transactionSourceAuthorizationLoan. iIntros "Hborrowed".
  iApply (transactions_source_authorization_restore_emptynonempty sp base bytes processed index
    dataBytes accessBytes chainBytes entries auth authBytes Q
    with "Hborrowed Hremaining").
Qed.
Print Assumptions transactions_source_authorization_memory_emptynonempty.
