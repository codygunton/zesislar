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
  WriteSuccessExactTransactionsSourceAuthorizationLoanRemainder.

Lemma transactions_source_authorization_restore_nonemptynonempty `{!islaG Sigma} `{!threadG}
    sp base bytes processed index dataBytes accessBytes chainBytes entries
    (blob : bv 8) (blobBytes : list (bv 8))
    (auth : bv 8) (authBytes : list (bv 8))
    (Q : iProp Sigma) :
  transactionSourceAuthorizationBorrowed sp bytes index (auth :: authBytes) -∗
  transactionSourceAuthorizationLoanRemainder sp base bytes processed index dataBytes accessBytes
    chainBytes entries (blob :: blobBytes) Q -∗
  transactionSourceBlobFeeRetained sp base bytes processed index dataBytes accessBytes
    chainBytes entries (blob :: blobBytes)
    (writeSuccessByteArrayOwn (transactionRowWord bytes index 240) (auth :: authBytes) ∗ Q)%I.
Proof.
  iIntros "Hborrowed Hremaining".
  iEval (unfold transactionSourceAuthorizationLoanRemainder) in "Hremaining".
  iDestruct "Hremaining" as (pointer storedIndex) "(%HstackHigh & Hremaining)".
  iDestruct "Hremaining" as
    "(H19 & H22 & Hregs & Hblob & Hcount & Haccess & Hentries & HaccessBase & HaccessCount & HaccessIndex & Hkeys & Hremaining)".
  iDestruct "Hkeys" as (key0 key1 key2 key3) "Hkeys".
  iEval (unfold transactionSourceAuthorizationBorrowed, writeSuccessByteArrayOwn) in "Hborrowed".
  iEval (unfold writeSuccessByteArrayOwn) in "Hblob".
  iEval (cbn) in "Hregs".
  zesu_open_resource_groups; zesu_open_bits_registers.
  unfold transactionSourceBlobFeeRetained, transactionFieldSourceFeeRest, writeSuccessByteArrayOwn.
  let shapes := eval vm_compute in WriteSuccessExactBlobHashesAuthorizationEntry.blobAuthorizationRemainingShapes in
  replace WriteSuccessExactBlobHashesAuthorizationEntry.blobAuthorizationRemainingShapes with shapes by reflexivity.
  cbn; zesu_run; try bv_solve; try zesu_handoff.
Qed.
Print Assumptions transactions_source_authorization_restore_nonemptynonempty.
