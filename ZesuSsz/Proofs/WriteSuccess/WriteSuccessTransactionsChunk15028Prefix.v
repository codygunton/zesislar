Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15028.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15044.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.

Ltac solve_write_success_15028_prefix :=
  try prepare_sidecond;
  try assumption;
  try bv_solve;
  try lia;
  try iFrame.

Lemma write_success_transactions_chunk_15028_prefix
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15044 (writeSuccessTransactionsAt15044Spec P) -∗
  instr_body 0x15028 (writeSuccessTransactionsAt15028Spec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve. all: solve_write_success_15028_prefix.
  Unshelve.
  all: iExists (tail, suffix, prefix, bytes, remaining, processed,
    transactions, transaction, base, sp, tt)ₗ.
  all: rewrite /writeSuccessTransactionsMachine15044
    /writeSuccessTransactionsScratch15044.
  all: iRename select
    ((bv_unsigned sp + 128 + 8) ↦ₘ? 88)%I into "Hscratch136".
  all: iEval (replace (bv_unsigned sp + 128 + 8)%Z with
    (bv_unsigned sp + 136)%Z by lia) in "Hscratch136".
  all: iFrame.
  all: try done.
Qed.
