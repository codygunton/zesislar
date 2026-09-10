Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderInt1645Call.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderU256.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary153d0.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk153d0.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk15564.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk15574.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk1558cBranch.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBodySuffixFinal.

Lemma write_success_transactions_body_suffix_late_prefix
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x153d4 (writeSuccessBlobHashesLoopSpec P) -∗
  □ instr_pre 0x15590
    (writeSuccessTransactionsAuthorizationsAnyLoopSpec P) -∗
  □ instr_pre 0x15cb0 zesuEncoderU256CallSpec -∗
  □ instr_pre 0x15ce4 zesuEncoderInt1645CallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x14f04 (writeSuccessTransactionsLoopSpec P) -∗
  instr_body 0x153d0 (writeSuccessTransactionsAt153d0Spec P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hmemcpy #Houtput #Hblob #Hauth #Hu256 #Hint128 #Hint64 #Hloop".
  iApply (write_success_transactions_chunk_153d0 P with
    "Hlookup Hcode Houtput Hblob").
  iApply (write_success_transactions_chunk_15564 P with
    "Hlookup Hcode Hint128").
  iApply (write_success_transactions_chunk_15574 P with
    "Hlookup Hcode Hint64").
  iApply (write_success_transactions_body_suffix_final P with
    "Hlookup Hcode Hmemcpy Houtput Hauth Hu256 Hint64 Hloop").
Qed.
