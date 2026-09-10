Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState1504c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15054.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk1504c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk15050Raw.

Lemma write_success_transactions_carrier_chunk_1504c_to_15054
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15054 (writeSuccessTransactionsAt15054CarrierSpec P) -∗
  instr_body 0x1504c (writeSuccessTransactionsAt1504cCarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iApply (write_success_transactions_carrier_chunk_1504c with
    "Hlookup Hcode").
  iApply (write_success_transactions_carrier_chunk_15050 with
    "Hlookup Hcode Hnext").
Qed.
