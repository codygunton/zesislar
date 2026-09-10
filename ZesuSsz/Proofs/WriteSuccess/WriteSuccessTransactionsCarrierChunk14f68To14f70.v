From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisCode.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f68.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f70.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk14f68Raw.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk14f6cRaw.

Lemma write_success_transactions_carrier_chunk_14f68_to_14f70
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f70 (writeSuccessTransactionsAt14f70CarrierSpec P) -∗
  instr_body 0x14f68 (writeSuccessTransactionsAt14f68CarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iPoseProof (write_success_transactions_carrier_chunk_14f6c_raw P with
    "Hlookup Hcode Hnext") as "H14f6c".
  iApply (write_success_transactions_carrier_chunk_14f68_raw P with
    "Hlookup Hcode H14f6c").
Qed.
