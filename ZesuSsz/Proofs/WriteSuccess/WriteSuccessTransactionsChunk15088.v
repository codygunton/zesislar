Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15088.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15088Load.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk1508c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15090Load.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15094.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15098.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk1509cLoad.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150a0Load.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150a4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150a8Load.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150ac.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150b0Load.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150b4Load.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150b8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150bcLoad.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150c0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150c4Load.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150c8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150ccLoad.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150d0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150d4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150d8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150dc.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150e0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150e4.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_15088
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x150e8 (writeSuccessTransactionsAt150e8Spec P) -∗
  instr_body 0x15088 (writeSuccessTransactionsAt15088Spec P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode Hnext".
  iApply (write_success_transactions_chunk_15088_load P with
    "Hlookup Hcode").
  iApply (write_success_transactions_chunk_1508c P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_15090_load P with
    "Hlookup Hcode").
  iApply (write_success_transactions_chunk_15094 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_15098 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_1509c_load P with
    "Hlookup Hcode").
  iApply (write_success_transactions_chunk_150a0_load P with
    "Hlookup Hcode").
  iApply (write_success_transactions_chunk_150a4 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_150a8_load P with
    "Hlookup Hcode").
  iApply (write_success_transactions_chunk_150ac P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_150b0_load P with
    "Hlookup Hcode").
  iApply (write_success_transactions_chunk_150b4_load P with
    "Hlookup Hcode").
  iApply (write_success_transactions_chunk_150b8 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_150bc_load P with
    "Hlookup Hcode").
  iApply (write_success_transactions_chunk_150c0 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_150c4_load P with
    "Hlookup Hcode").
  iApply (write_success_transactions_chunk_150c8 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_150cc_load P with
    "Hlookup Hcode").
  iApply (write_success_transactions_chunk_150d0 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_150d4 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_150d8 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_150dc P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_150e0 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_150e4 P with "Hlookup Hcode").
  iExact "Hnext".
Qed.
