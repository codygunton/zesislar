Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15584.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk1558cBranch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15584.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15620.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk1562c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15644.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsTail.

Lemma write_success_transactions_body_suffix_final
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15590
    (writeSuccessTransactionsAuthorizationsAnyLoopSpec P) -∗
  □ instr_pre 0x15cb0 zesuEncoderU256CallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x14f04 (writeSuccessTransactionsLoopSpec P) -∗
  instr_body 0x15584 (writeSuccessTransactionsAt15584Spec P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hmemcpy #Houtput #Hauth #Hu256 #Hint64 #Hloop".
  iApply (write_success_transactions_chunk_15584 P with
    "Hlookup Hcode Hmemcpy Hu256 Hint64 Houtput Hauth").
  iApply (write_success_transactions_chunk_15620 P with
    "Hlookup Hcode Hint64").
  iApply (write_success_transactions_chunk_1562c P with
    "Hlookup Hcode Hu256").
  iApply (write_success_transactions_chunk_15644 P with
    "Hlookup Hcode Hu256").
  iApply (write_success_transactions_tail P with
    "Hlookup Hcode Hloop").
Qed.
