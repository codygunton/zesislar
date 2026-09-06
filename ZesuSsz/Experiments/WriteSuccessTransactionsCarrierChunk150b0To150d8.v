Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState150b0.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState150d8.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierChunk150b0Raw.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierChunk150b4Raw.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierChunk150b8.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierChunk150bcRaw.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierChunk150c0.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierChunk150c4Raw.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierChunk150c8.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierChunk150ccRaw.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierChunk150d0.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierChunk150d4.

Lemma write_success_transactions_carrier_chunk_150b0_to_150d8
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x150d8 (writeSuccessTransactionsAt150d8CarrierSpec P) -∗
  instr_body 0x150b0 (writeSuccessTransactionsAt150b0CarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iApply (write_success_transactions_carrier_chunk_150b0 with "Hlookup Hcode").
  iApply (write_success_transactions_carrier_chunk_150b4 with "Hlookup Hcode").
  iApply (write_success_transactions_carrier_chunk_150b8 with "Hlookup Hcode").
  iApply (write_success_transactions_carrier_chunk_150bc with "Hlookup Hcode").
  iApply (write_success_transactions_carrier_chunk_150c0 with "Hlookup Hcode").
  iApply (write_success_transactions_carrier_chunk_150c4 with "Hlookup Hcode").
  iApply (write_success_transactions_carrier_chunk_150c8 with "Hlookup Hcode").
  iApply (write_success_transactions_carrier_chunk_150cc with "Hlookup Hcode").
  iApply (write_success_transactions_carrier_chunk_150d0 with "Hlookup Hcode").
  iApply (write_success_transactions_carrier_chunk_150d4 with
    "Hlookup Hcode Hnext").
Qed.
