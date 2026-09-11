Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15574.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15584.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15574Entry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15580Call.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_15574
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x15584 (writeSuccessTransactionsAt15584Spec P) -∗
  instr_body 0x15574 (writeSuccessTransactionsAt15574Spec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hint Hnext".
  iApply write_success_transactions_chunk_15574_entry;
    [iExact "Hlookup" | iExact "Hcode" |].
  iApply write_success_transactions_chunk_15580_call;
    [iExact "Hlookup" | iExact "Hcode" | iExact "Hint" | iExact "Hnext"].
Qed.
