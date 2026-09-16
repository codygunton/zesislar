Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256Spec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15644.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1565c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15644Entry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15658Call.

Lemma write_success_transactions_chunk_15644
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15cb0 zesuEncoderU256CallSpec -∗
  instr_body 0x1565c (writeSuccessTransactionsAt1565cSpec P) -∗
  instr_body 0x15644 (writeSuccessTransactionsAt15644Spec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hu256 Hnext".
  iApply write_success_transactions_chunk_15644_entry;
    [iExact "Hlookup" | iExact "Hcode" |].
  iApply write_success_transactions_chunk_15658_call;
    [iExact "Hlookup" | iExact "Hcode" | iExact "Hu256" | iExact "Hnext"].
Qed.
