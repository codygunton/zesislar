Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk1558cBranch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBytesCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderInt1645Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBodySuffixMiddle.

Lemma write_success_transactions_body_suffix
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x153d4 (writeSuccessBlobHashesLoopSpec P) -∗
  □ instr_pre 0x15590
    (writeSuccessTransactionsAuthorizationsAnyLoopSpec P) -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  □ instr_pre 0x15cb0 zesuEncoderU256CallSpec -∗
  □ instr_pre 0x15ce4 zesuEncoderInt1645CallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x14f04 (writeSuccessTransactionsLoopSpec P) -∗
  instr_body 0x1519c (writeSuccessTransactionsAt1519cSpec P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hmemcpy #Houtput #Hblob #Hauth #Hbytes #Hu256
    #Hint128 #Hint64 #Hloop".
  iApply (write_success_transactions_chunk_1519c P with
    "Hlookup Hcode Hu256").
  iApply (write_success_transactions_body_suffix_middle P with
    "Hlookup Hcode Hmemcpy Houtput Hblob Hauth Hbytes Hu256 Hint128 Hint64 Hloop").
Qed.
