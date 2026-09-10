From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15620.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary1562c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk15620Entry.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk15628Call.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_15620
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x1562c (writeSuccessTransactionsAt1562cSpec P) -∗
  instr_body 0x15620 (writeSuccessTransactionsAt15620Spec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hint Hnext".
  iApply write_success_transactions_chunk_15620_entry;
    [iExact "Hlookup" | iExact "Hcode" |].
  iApply write_success_transactions_chunk_15628_call;
    [iExact "Hlookup" | iExact "Hcode" | iExact "Hint" | iExact "Hnext"].
Qed.
