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
  WriteSuccessExactTransactionsSourceAuthorizationLoanEmptyEmpty
  WriteSuccessExactTransactionsSourceAuthorizationLoanEmptyNonempty
  WriteSuccessExactTransactionsSourceAuthorizationLoanNonemptyEmpty
  WriteSuccessExactTransactionsSourceAuthorizationLoanNonemptyNonempty.

Lemma transactions_source_authorization_memory_frame `{!islaG Sigma} `{!threadG}
    sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes authBytes
    (Q : iProp Sigma) :
  (bv_unsigned sp + 1896 < machineRamEnd defaultMap)%Z ->
  transactionSourceBlobFeeRetained sp base bytes processed index dataBytes accessBytes
    chainBytes entries blobBytes
    (writeSuccessByteArrayOwn (transactionRowWord bytes index 240) authBytes ∗ Q)%I -∗
  transactionSourceAuthorizationBorrowed sp bytes index authBytes ∗
  transactionSourceAuthorizationLoan sp base bytes processed index dataBytes accessBytes
    chainBytes entries blobBytes authBytes Q.
Proof.
  intros HstackHigh.
  destruct blobBytes as [|blob blobBytes]; destruct authBytes as [|auth authBytes].
  - apply transactions_source_authorization_memory_emptyempty; assumption.
  - apply transactions_source_authorization_memory_emptynonempty; assumption.
  - apply transactions_source_authorization_memory_nonemptyempty; assumption.
  - apply transactions_source_authorization_memory_nonemptynonempty; assumption.
Qed.
Print Assumptions transactions_source_authorization_memory_frame.
