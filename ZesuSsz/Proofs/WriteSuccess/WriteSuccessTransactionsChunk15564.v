From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderInt1645Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15564.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15574.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15564Entry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15570Call.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_15564
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15ce4 zesuEncoderInt1645CallSpec -∗
  instr_body 0x15574 (writeSuccessTransactionsAt15574Spec P) -∗
  instr_body 0x15564 (writeSuccessTransactionsAt15564Spec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hint Hnext".
  iApply write_success_transactions_chunk_15564_entry;
    [iExact "Hlookup" | iExact "Hcode" |].
  iApply write_success_transactions_chunk_15570_call;
    [iExact "Hlookup" | iExact "Hcode" | iExact "Hint" | iExact "Hnext"].
Qed.
