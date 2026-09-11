Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150ec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150f0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150ecEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150ecJump.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk10190Call.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
Local Opaque writeSuccessTransactionPhaseEvents.

Lemma write_success_transactions_chunk_150ec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_body 0x150f0 (writeSuccessTransactionsAt150f0Spec P) -∗
  instr_body 0x150ec (writeSuccessTransactionsAt150ecSpec P).
Proof.
  iIntros "#Hlookup _ #Houtput Hnext".
  iApply write_success_transactions_chunk_150ec_entry.
  iApply (write_success_transactions_chunk_150ec_jump with "Hlookup").
  iApply (write_success_transactions_chunk_10190_call with "Houtput Hnext").
Qed.
