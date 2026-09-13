Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f90.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f98.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f90.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f98.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPuncturedScratch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseCarrierFrame.

Lemma write_success_transactions_carrier_chunk_14f90
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f98 (writeSuccessTransactionsAt14f98CarrierSpec P) -∗
  instr_body 0x14f90 (writeSuccessTransactionsAt14f90CarrierSpec P).
Proof.
  move => *. iStartProof. iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  zesu_run.
  Unshelve. all: repeat iIntros "?"; zesu_run.
  Unshelve.
  all: try (liInst (fun x => x.9ₗ = bytes /\ x.8ₗ = prefix /\
    x.7ₗ = suffix /\ x.6ₗ = tail); zesu_run).
  Unshelve. all: try zesu_handoff.
  Unshelve. all: try zesu_finish.
  Unshelve. all: try zesu_frame_handoff.
  Unshelve. all: try zesu_finish.
Qed.

Print Assumptions write_success_transactions_carrier_chunk_14f90.
