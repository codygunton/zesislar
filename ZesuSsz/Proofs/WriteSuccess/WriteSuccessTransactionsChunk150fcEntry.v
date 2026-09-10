From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150fc.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15104.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk150fcLoad.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk150fcAuipc.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_150fc_entry
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15104 (writeSuccessTransactionsAt15104Spec P) -∗
  instr_body 0x150fc (writeSuccessTransactionsAt150fcSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iApply write_success_transactions_chunk_150fc_load;
    [iExact "Hlookup" | iExact "Hcode" |].
  iApply write_success_transactions_chunk_15100_auipc;
    [iExact "Hlookup" | iExact "Hcode" | iExact "Hnext"].
Qed.
