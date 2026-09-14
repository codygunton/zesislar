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
  WriteSuccessExactAuthorizationsCountInitial WriteSuccessExactAuthorizationsLoopSpec
  WriteSuccessExactAuthorizationsInitial.

Lemma transactions_source_authorization_loop_exit `{!islaG Sigma} `{!threadG}
    sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes authBytes
    authRest tail (Q : iProp Sigma) :
  transactionRowWord bytes index 248 = Z_to_bv 64 (Z.of_nat (S (length authRest))) ->
  (mapRamBase defaultMap <= bv_unsigned (transactionRowWord bytes index 240))%Z ->
  (bv_unsigned (transactionRowWord bytes index 240) + Z.of_nat (length authBytes) < machineRamEnd defaultMap)%Z ->
  authorizationLoopExit sp (bv_unsigned (transactionRowWord bytes index 240)) authBytes tail
    (authorizationInitialFrame sp (bv_unsigned (transactionRowWord bytes index 240))
      (authorizationFeeFrame sp (transactionRowWord bytes index 80) (transactionRowWord bytes index 88)
        authRest (transactionSourceAuthorizationLoan sp base bytes processed index dataBytes accessBytes
          chainBytes entries blobBytes authBytes Q))) -∗
  transactionSourceAuthorizationExit sp base bytes processed index dataBytes accessBytes chainBytes
    entries blobBytes authBytes tail Q.
Proof.
  intros Hcount Hlow Hhigh.
  unfold authorizationLoopExit, authorizationInitialFrame, authorizationFeeFrame.
  iIntros "(Hsys & Hsp & H1 & H5 & H8 & H9 & H18 & Hregs & Hsource & Hcopy & Hscratch & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hpointer & (HfeeHigh & HfeeLow & Hcount & Hloan & _) & _)".
  iEval (rewrite Z_to_bv_bv_unsigned) in "Hpointer".
  iEval (rewrite -Hcount) in "Hcount".
  iAssert ((transactionSourceAuthorizationBorrowed sp bytes index authBytes ∗
    (bv_unsigned sp - 32) ↦ₘ? 32 ∗
    reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64)] ∗ True)%I)
    with "[H8 H9 Hregs Hsource Hcopy Hscratch Hpointer]" as "(Hborrowed & Hupper & Hpair & _)".
  { destruct authBytes as [|a authBytes];
      unfold transactionSourceAuthorizationBorrowed, writeSuccessByteArrayOwn;
      zesu_open_resource_groups; zesu_open_bits_registers; cbn; zesu_run. }
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
  destruct blobBytes; destruct authBytes; cbn;
    zesu_open_resource_groups; zesu_open_bits_registers; zesu_run; try zesu_handoff.
Qed.
Print Assumptions transactions_source_authorization_loop_exit.
