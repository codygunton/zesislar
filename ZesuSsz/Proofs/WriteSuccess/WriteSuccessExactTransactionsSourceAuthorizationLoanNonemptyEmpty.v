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

Lemma transactions_source_authorization_memory_nonemptyempty `{!islaG Sigma} `{!threadG}
    sp base bytes processed index dataBytes accessBytes chainBytes entries
    (blob : bv 8) (blobBytes : list (bv 8))
    (Q : iProp Sigma) :
  (bv_unsigned sp + 1896 < machineRamEnd defaultMap)%Z ->
  transactionSourceBlobFeeRetained sp base bytes processed index dataBytes accessBytes
    chainBytes entries (blob :: blobBytes)
    (writeSuccessByteArrayOwn (transactionRowWord bytes index 240) [] ∗ Q)%I -∗
  transactionSourceAuthorizationBorrowed sp bytes index [] ∗
  transactionSourceAuthorizationLoan sp base bytes processed index dataBytes accessBytes
    chainBytes entries (blob :: blobBytes) [] Q.
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
  unfold transactionSourceAuthorizationLoan, transactionSourceAuthorizationBorrowed,
    transactionSourceBlobFeeRetained, transactionFieldSourceFeeRest, writeSuccessByteArrayOwn;
  cbn; zesu_run; try bv_solve.
Qed.
Print Assumptions transactions_source_authorization_memory_nonemptyempty.
