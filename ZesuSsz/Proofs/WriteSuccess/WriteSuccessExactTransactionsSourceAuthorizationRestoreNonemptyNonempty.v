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
  WriteSuccessExactTransactionsSourceAuthorizationLoanRemainder
  WriteSuccessExactTransactionsSourceAuthorizationRestoreResources.

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
  iDestruct "Hremaining" as "(Hlast & Hremaining)".
  iEval (unfold transactionSourceAuthorizationBorrowed) in "Hborrowed".
  iDestruct "Hborrowed" as "(Hpair & Hquad & Hauth & Hscratch & Hlower & HauthPtr & _)".
  iPoseProof (transactions_source_authorization_restore_scratch sp with
    "Hscratch Hlast") as "[Hscratch40 Hscratch112]".
  iPoseProof (transactions_source_authorization_restore_registers with
    "Hpair Hquad Hregs") as "Hregs".
  iEval (unfold writeSuccessByteArrayOwn) in "Hauth Hblob".
  zesu_open_resource_groups.
  unfold transactionSourceBlobFeeRetained, transactionFieldSourceFeeRest, writeSuccessByteArrayOwn.
  let shapes := eval vm_compute in WriteSuccessExactBlobHashesAuthorizationEntry.blobAuthorizationRemainingShapes in
  replace WriteSuccessExactBlobHashesAuthorizationEntry.blobAuthorizationRemainingShapes with shapes by reflexivity.
  cbn. iExists pointer, storedIndex. iFrame; try (iPureIntro; eauto).
  repeat split; simpl in *; try lia; try assumption.
Qed.
Print Assumptions transactions_source_authorization_restore_nonemptynonempty.
