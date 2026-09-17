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
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14fb0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14fb4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessInstrBodyAdapters.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierPostLbu14fb0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk14fb0Head.

#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseCarrierFrame.
#[local] Typeclasses Opaque writeSuccessTransactionsInvariant.

Lemma write_success_transactions_carrier_chunk_14fb0_raw
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14fb4 (writeSuccessTransactionsAt14fb4CarrierSpec P) -∗
  instr_body 0x14fb0 (writeSuccessTransactionsAt14fb0CarrierSpec P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iPoseProof (instr_body_wand_adapter 0x14fb4
    (writeSuccessTransactionsAt14fb4CarrierSpec P)
    (writeSuccessTransactionsAt14fb4CarrierSplitSpec P)
    with "[] Hnext") as "HsplitNext".
  { iApply transaction_carrier_14fb4_split_restores_exact. }
  iApply (write_success_transactions_carrier_chunk_14fb0_head P
    with "[] Hcode HsplitNext").
  iExact "Hlookup".
Qed.
Print Assumptions write_success_transactions_carrier_chunk_14fb0_raw.
