Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15090.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState150b0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk15090Raw.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk15094.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk15098.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk1509cRaw.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk150a0Raw.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk150a4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk150a8Raw.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk150ac.

Lemma write_success_transactions_carrier_chunk_15090_to_150b0
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x150b0 (writeSuccessTransactionsAt150b0CarrierSpec P) -∗
  instr_body 0x15090 (writeSuccessTransactionsAt15090CarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iApply (write_success_transactions_carrier_chunk_15090 with
    "Hlookup Hcode").
  iApply (write_success_transactions_carrier_chunk_15094 with
    "Hlookup Hcode").
  iApply (write_success_transactions_carrier_chunk_15098 with
    "Hlookup Hcode").
  iApply (write_success_transactions_carrier_chunk_1509c with
    "Hlookup Hcode").
  iApply (write_success_transactions_carrier_chunk_150a0 with
    "Hlookup Hcode").
  iApply (write_success_transactions_carrier_chunk_150a4 with
    "Hlookup Hcode").
  iApply (write_success_transactions_carrier_chunk_150a8 with
    "Hlookup Hcode").
  iApply (write_success_transactions_carrier_chunk_150ac with
    "Hlookup Hcode Hnext").
Qed.
