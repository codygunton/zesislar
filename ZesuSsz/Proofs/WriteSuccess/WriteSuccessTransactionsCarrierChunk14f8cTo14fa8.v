From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisCode.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f8c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14fa8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk14f8cRaw.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk14f90.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk14f98Raw.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk14f9cRaw.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk14fa0Raw.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk14fa4Raw.

Lemma write_success_transactions_carrier_chunk_14f8c_to_14fa8
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14fa8 (writeSuccessTransactionsAt14fa8CarrierSpec P) -∗
  instr_body 0x14f8c (writeSuccessTransactionsAt14f8cCarrierSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iPoseProof (write_success_transactions_carrier_chunk_14fa4_raw P with
    "Hlookup Hcode Hnext") as "Ha4".
  iPoseProof (write_success_transactions_carrier_chunk_14fa0_raw P with
    "Hlookup Hcode Ha4") as "Ha0".
  iPoseProof (write_success_transactions_carrier_chunk_14f9c_raw P with
    "Hlookup Hcode Ha0") as "H9c".
  iPoseProof (write_success_transactions_carrier_chunk_14f98_raw P with
    "Hlookup Hcode H9c") as "H98".
  iPoseProof (write_success_transactions_carrier_chunk_14f90 P with
    "Hlookup Hcode H98") as "H90".
  iApply (write_success_transactions_carrier_chunk_14f8c_raw P with
    "Hlookup Hcode H90").
Qed.
