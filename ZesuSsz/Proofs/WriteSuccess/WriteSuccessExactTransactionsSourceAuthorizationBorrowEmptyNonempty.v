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

Lemma transactions_source_authorization_borrow_emptynonempty `{!islaG Sigma} `{!threadG}
    sp base bytes processed index dataBytes accessBytes chainBytes entries
    (auth : bv 8) (authBytes : list (bv 8))
    (Q : iProp Sigma) :
  (bv_unsigned sp + 1896 < machineRamEnd defaultMap)%Z ->
  transactionSourceBlobFeeRetained sp base bytes processed index dataBytes accessBytes
    chainBytes entries []
    (writeSuccessByteArrayOwn (transactionRowWord bytes index 240) (auth :: authBytes) ∗ Q)%I -∗
  transactionSourceAuthorizationBorrowed sp bytes index (auth :: authBytes) ∗
  transactionSourceAuthorizationLoanRemainder sp base bytes processed index dataBytes accessBytes
    chainBytes entries [] Q.
Proof.
  intros HstackHigh.
  iStartProof; iIntros "Hframe";
  iEval (unfold transactionSourceBlobFeeRetained) in "Hframe";
  iDestruct "Hframe" as (pointer storedIndex)
    "(H19 & H22 & Hregs & Hblob & Hcount & Haccess & Hown & HaccessBase & HaccessCount &
      HaccessIndex & Hcopy & Hkeys & Hlower & Hrec0 & Hrec1 & Hrec2 & Htag & Hvalue &
      Hdata & Hchain & Hmemory & _)";
  iDestruct "Hkeys" as (key0 key1 key2 key3) "Hkeys";
  iEval (unfold transactionFieldSourceFeeRest, writeSuccessByteArrayOwn) in "Hmemory Hblob";
  let shapes := eval vm_compute in WriteSuccessExactBlobHashesAuthorizationEntry.blobAuthorizationRemainingShapes in
  iEval (replace WriteSuccessExactBlobHashesAuthorizationEntry.blobAuthorizationRemainingShapes
    with shapes by reflexivity) in "Hregs";
  zesu_open_resource_groups;
  zesu_open_bits_registers;
  unfold transactionSourceAuthorizationLoanRemainder, transactionSourceAuthorizationBorrowed,
    transactionFieldSourceFeeRest, writeSuccessByteArrayOwn;
  cbn; zesu_run; try bv_solve.
Qed.
Print Assumptions transactions_source_authorization_borrow_emptynonempty.
