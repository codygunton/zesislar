Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15088.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15090.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk15088Raw.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk1508c.

Lemma write_success_transactions_carrier_chunk_15088_to_15090
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15090 (writeSuccessTransactionsAt15090CarrierSpec P) -∗
  instr_body 0x15088 (writeSuccessTransactionsAt15088CarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iApply (write_success_transactions_carrier_chunk_15088 with
    "Hlookup Hcode").
  iApply (write_success_transactions_carrier_chunk_1508c with
    "Hlookup Hcode Hnext").
Qed.
