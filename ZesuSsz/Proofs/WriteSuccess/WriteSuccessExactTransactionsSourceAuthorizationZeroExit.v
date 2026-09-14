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
  WriteSuccessExactTransactionsSourceAuthorizationZeroSpec WriteSuccessExactAuthorizationsInitialZero.

Lemma transactions_source_authorization_zero_exit `{!islaG Sigma} `{!threadG}
    sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes tail (Q : iProp Sigma) :
  authorizationZeroPost sp (transactionRowWord bytes index 240) tail
    (transactionSourceAuthorizationZeroFrame sp base bytes processed index dataBytes accessBytes
      chainBytes entries blobBytes Q) -∗
  transactionSourceAuthorizationExit sp base bytes processed index dataBytes accessBytes chainBytes
    entries blobBytes [] tail Q.
Proof.
  unfold authorizationZeroPost, transactionSourceAuthorizationZeroFrame.
  iIntros "(Hsys & Hsp & H8 & H9 & H18 & Hpointer & %Halign & %Hlow & %Hhigh & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(HzeroRegs & H12 & Hcopy & Hlower & Hupper & HfeeHigh & HfeeLow & Hcount & Hloan & Hmmio & _)".
  iAssert (transactionSourceAuthorizationBorrowed sp bytes index [])%I
    with "[H8 H9 H12 Hcopy Hlower Hpointer]" as "Hborrowed".
  { unfold transactionSourceAuthorizationBorrowed, writeSuccessByteArrayOwn; cbn;
    zesu_open_resource_groups; zesu_open_bits_registers; zesu_run. }
  iEval (unfold transactionSourceAuthorizationLoan) in "Hloan".
  iPoseProof ("Hloan" with "Hborrowed") as "Hframe".
  iEval (unfold transactionSourceBlobFeeRetained) in "Hframe".
  iDestruct "Hframe" as (pointer storedIndex) "Hframe".
  iDestruct "Hframe" as
    "(H19 & H22 & Hregs & Hblob & HblobCount & Haccess & Hown & HaccessBase & HaccessCount &
      HaccessIndex & Hcopy & Hkeys & Hlower & Hrec0 & Hrec1 & Hrec2 & Htag & Hvalue &
      Hdata & Hchain & Hmemory & _)".
  iDestruct "Hkeys" as (key0 key1 key2 key3) "Hkeys".
  iEval (unfold transactionFieldSourceFeeRest, writeSuccessByteArrayOwn) in "Hmemory Hblob".
  unfold transactionSourceAuthorizationExit, transactionFieldSourceFeeRest, writeSuccessByteArrayOwn.
  destruct blobBytes; cbn;
  zesu_open_resource_groups; zesu_open_bits_registers; zesu_run; try zesu_handoff.
Qed.
Print Assumptions transactions_source_authorization_zero_exit.
