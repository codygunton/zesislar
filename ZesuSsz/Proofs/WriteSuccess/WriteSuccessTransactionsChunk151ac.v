Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary151b4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151acAuipc.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151acSetup.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151b0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151b0Prepare.

Lemma write_success_transactions_chunk_151ac
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15cb0 zesuEncoderU256CallSpec -∗
  instr_body 0x151b4 (writeSuccessTransactionsAt151b4Spec P) -∗
  instr_body 0x151ac (writeSuccessTransactionsAt151acSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Hu256 Hnext".
  iPoseProof (write_success_transactions_chunk_151b0_core with
    "Hlookup Hu256") as "HjalrCore".
  iAssert (instr_body 0x151b0 (writeSuccessTransactions151b0SetupSpec P))%I
    with "[HjalrCore]" as "Hjalr".
  { iEval (rewrite instr_pre'_eq) in "HjalrCore".
    rewrite instr_pre'_eq. iIntros "Hsetup".
    iApply "HjalrCore".
    iApply (write_success_transactions_151b0_prepare P with "Hsetup"). }
  iPoseProof (write_success_transactions_chunk_151ac_auipc P with
    "Hlookup Hcode Hjalr") as "Hcore".
  iEval (rewrite instr_pre'_eq) in "Hcore".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iPoseProof (write_success_transactions_151ac_setup P) as "Hsetup".
  iEval (rewrite instr_pre'_eq) in "Hsetup".
  iSpecialize ("Hsetup" with "Hnext Hentry").
  iApply "Hcore".
  iExact "Hsetup".
Qed.
