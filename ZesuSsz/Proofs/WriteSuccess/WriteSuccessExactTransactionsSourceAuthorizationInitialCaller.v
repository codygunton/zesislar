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

Lemma transactions_source_authorization_initial_caller `{!islaG Sigma} `{!threadG}
    sp low high bytes index row rest authBytes tail (P : iProp Sigma) :
  authorizationLoopFacts sp (transactionRowWord bytes index 240)
    (bv_unsigned (transactionRowWord bytes index 240)) (row :: rest) [] row rest authBytes ->
  transactionSourceAuthorizationBorrowed sp bytes index authBytes -∗ P -∗
  instr_pre 0x15620 (authorizationLoopExit sp (bv_unsigned (transactionRowWord bytes index 240))
    authBytes tail (authorizationInitialFrame sp (bv_unsigned (transactionRowWord bytes index 240))
      (authorizationFeeFrame sp low high rest P))) -∗
  authorizationInitialCaller sp low high (bv_unsigned (transactionRowWord bytes index 240))
    row rest authBytes tail P.
Proof.
  intros Hfacts. destruct authBytes as [|a authBytes].
  - exfalso. destruct Hfacts as (_ & Hrows & Hsource & _).
    inversion Hrows as [|row0 rest0 HrowLength Hrest]; subst.
    apply (f_equal (@length (bv 8))) in Hsource.
    cbn in Hsource. rewrite app_length in Hsource. lia.
  - iIntros "Hborrowed HP Hnext".
    iEval (unfold transactionSourceAuthorizationBorrowed, writeSuccessByteArrayOwn) in "Hborrowed".
    unfold authorizationInitialCaller. rewrite Z_to_bv_bv_unsigned.
    cbn. zesu_open_resource_groups. zesu_open_bits_registers. zesu_run.
Qed.
Print Assumptions transactions_source_authorization_initial_caller.
