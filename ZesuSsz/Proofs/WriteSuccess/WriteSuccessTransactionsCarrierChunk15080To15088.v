Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState15080.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState15088.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierChunk15080Raw.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierChunk15084.

Lemma write_success_transactions_carrier_chunk_15080_to_15088
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15088 (writeSuccessTransactionsAt15088CarrierSpec P) -∗
  instr_body 0x15080 (writeSuccessTransactionsAt15080CarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iApply (write_success_transactions_carrier_chunk_15080 with
    "Hlookup Hcode").
  iApply (write_success_transactions_carrier_chunk_15084 with
    "Hlookup Hcode Hnext").
Qed.
