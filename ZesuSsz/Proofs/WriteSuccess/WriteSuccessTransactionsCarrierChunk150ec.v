Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrier10190Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierCall150ec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk150ecCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState150ec.

Lemma write_success_transactions_carrier_chunk_150ec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_body 0x150f0 (writeSuccessTransactionsAt150f0CarrierCallSpec P) -∗
  instr_body 0x150ec (writeSuccessTransactionsAt150ecCarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode #Houtput Hnext".
  iApply (write_success_transactions_carrier_chunk_150ec_jump with
    "Hlookup Hcode").
  iApply (write_success_transactions_carrier_10190_call with
    "Houtput Hnext").
Qed.
