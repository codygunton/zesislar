Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Lookup.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundarySpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f08Entry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f20.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f24.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f28.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f2c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f30.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f34.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f38.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f3c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f40.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f44.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f48.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f4c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f50.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f54.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f58.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f5c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f60.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f64.

Lemma write_success_transactions_chunk_14f08
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f68 (writeSuccessTransactionsAt14f68Spec P) -∗
  instr_body 0x14f08 (writeSuccessTransactionsAt14f08Spec P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode Hnext".
  iApply (write_success_transactions_chunk_14f08_entry P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f1c P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f20 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f24 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f28 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f2c P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f30 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f34 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f38 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f3c P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f40 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f44 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f48 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f4c P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f50 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f54 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f58 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f5c P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f60 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f64 P with "Hlookup Hcode").
  iExact "Hnext".
Qed.
