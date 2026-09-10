Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisCode.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f8c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14fc8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk14f8cTo14fa8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk14fa8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk14fb0Raw.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk14fb4.

Lemma write_success_transactions_carrier_chunk_14f8c_to_14fc8
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14fc8 (writeSuccessTransactionsAt14fc8CarrierSpec P) -∗
  instr_body 0x14f8c (writeSuccessTransactionsAt14f8cCarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iPoseProof (write_success_transactions_carrier_chunk_14fb4 P with
    "Hlookup Hcode Hnext") as "Hb4".
  iPoseProof (write_success_transactions_carrier_chunk_14fb0_raw P with
    "Hlookup Hcode Hb4") as "Hb0".
  iPoseProof (write_success_transactions_carrier_chunk_14fa8 P with
    "Hlookup Hcode Hb0") as "Ha8".
  iApply (write_success_transactions_carrier_chunk_14f8c_to_14fa8 P with
    "Hlookup Hcode Ha8").
Qed.
