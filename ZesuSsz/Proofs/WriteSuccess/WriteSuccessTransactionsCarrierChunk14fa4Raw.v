Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f5c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierBoundary14f68.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14fa4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14fa8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessInstrBodyAdapters.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierPostLbu14fa4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk14fa4Head.

#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseCarrierFrame.
#[local] Typeclasses Opaque writeSuccessTransactionsInvariant.

Lemma write_success_transactions_carrier_chunk_14fa4_raw
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14fa8 (writeSuccessTransactionsAt14fa8CarrierSpec P) -∗
  instr_body 0x14fa4 (writeSuccessTransactionsAt14fa4CarrierSpec P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iPoseProof (instr_body_wand_adapter 0x14fa8
    (writeSuccessTransactionsAt14fa8CarrierSpec P)
    (writeSuccessTransactionsAt14fa8CarrierSplitSpec P)
    with "[] Hnext") as "HsplitNext".
  { iApply transaction_carrier_14fa8_split_restores_exact. }
  iApply (write_success_transactions_carrier_chunk_14fa4_head P
    with "[] Hcode HsplitNext").
  iExact "Hlookup".
Qed.
Print Assumptions write_success_transactions_carrier_chunk_14fa4_raw.
