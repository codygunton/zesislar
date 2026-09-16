Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e8Adapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e8Phase.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150e4Phase.

Lemma write_success_transactions_body_150e8_phase_public
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_body 0x150e8 (writeSuccessTransactionsAt150e8Spec P) -∗
  instr_body 0x150e8 (writeSuccessTransactionsAt150e8PhaseSpec P).
Proof.
  rewrite !instr_pre'_eq.
  iIntros "Hnext Hphase".
  iApply "Hnext".
  iApply (write_success_transactions_at_150e8_phase_public with "Hphase").
Qed.

Lemma write_success_transactions_chunk_150e4
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x150e8 (writeSuccessTransactionsAt150e8Spec P) -∗
  instr_body 0x150e4 (writeSuccessTransactionsAt150e4Spec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iApply (write_success_transactions_chunk_150e4_phase with
    "Hlookup Hcode").
  iApply (write_success_transactions_body_150e8_phase_public with "Hnext").
Qed.
