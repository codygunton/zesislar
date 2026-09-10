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

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseCarrierFrame.

Lemma write_success_transactions_carrier_chunk_14f90
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f98 (writeSuccessTransactionsAt14f98CarrierSpec P) -∗
  instr_body 0x14f90 (writeSuccessTransactionsAt14f90CarrierSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: destruct H0 as
    (Hsecond & HitemsBound & HfirstAlign & HfirstLower & HfirstUpper &
      Hsp16Align & Hsp80Lower & HspRamUpper).
  all: try iRename select
    (writeSuccessTransactionsLoadFacts sp base transaction processed bytes ∗
      True)%I into "HfactsBundle".
  all: try iDestruct "HfactsBundle" as "[Hfacts _]".
  all: try iEval (unfold writeSuccessTransactionsLoadFacts) in "Hfacts".
  all: try iDestruct "Hfacts" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  all: try bv_solve.
  all: try lia.
  iRename select ((bv_unsigned sp + 1672 + 8) ↦ₘ? 64)%I
    into "Hscratch1680".
  have Hscratch1680Address :
      (bv_unsigned sp + 1672 + 8 = bv_unsigned sp + 1680)%Z by lia.
  iEval (rewrite Hscratch1680Address) in "Hscratch1680".
  iExists (items, fourth, third, second, first, tail, suffix, prefix,
    bytes, remaining, processed, transactions, transaction, base, sp, tt)ₗ.
  rewrite /writeSuccessTransactionsMachine14f98Carrier
    /writeSuccessTransactions14f98CarrierScratch
    /writeSuccessTransactionsCurrentPhaseCarrierFrame
    /writeSuccessTransactionsLoopCarrierPayload
    /writeSuccessTransactionsWordsCarrier
    /writeSuccessTransactionPhaseEvents /writeSuccessByteArrayOwn
    /writeSuccessTransactionsLoadFacts
    /WriteSuccessTransactionsPost15674Boundary.writeSuccessTransactionsPost15674ByteListFacts.
  iFrame "Hscratch1680".
  iFrame.
  repeat iSplit; try (iPureIntro; assumption); try done.
Qed.
