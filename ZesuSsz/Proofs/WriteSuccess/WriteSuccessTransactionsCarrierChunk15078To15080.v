Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15078.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15080.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk15078Raw.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk1507c.

Lemma write_success_transactions_carrier_chunk_15078_to_15080
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15080 (writeSuccessTransactionsAt15080CarrierSpec P) -∗
  instr_body 0x15078 (writeSuccessTransactionsAt15078CarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iApply (write_success_transactions_carrier_chunk_15078 with
    "Hlookup Hcode").
  iApply (write_success_transactions_carrier_chunk_1507c with
    "Hlookup Hcode Hnext").
Qed.
