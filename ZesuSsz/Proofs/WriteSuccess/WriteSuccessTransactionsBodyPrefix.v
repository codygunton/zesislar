Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderInt1645Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundarySpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f08.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f68.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f70.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f74.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f78.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f7c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f80.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f84.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f88.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f8c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f90.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f98.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14f9c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14fa0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14fa4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14fa8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14fb0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14fb4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14fc8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15028.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15048.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk1505c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15078.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15088.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150e8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150f0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150fc.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15108.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15118.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15148.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15154.

Lemma write_success_transactions_body_prefix
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  □ instr_pre 0x15bc8 zesuEncoderOptionalU64CallSpec -∗
  □ instr_pre 0x15ce4 zesuEncoderInt1645CallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x1519c (writeSuccessTransactionsAt1519cSpec P) -∗
  instr_body 0x14f08 (writeSuccessTransactionsAt14f08Spec P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Houtput #Hboolean #Hoptional
    #Hint128 #Hint64 Hnext".
  iApply (write_success_transactions_chunk_14f08 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f68 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f70 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f74 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f78 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f7c P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f80 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f84 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f88 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f8c P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f90 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f98 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14f9c P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14fa0 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14fa4 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14fa8 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14fb0 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14fb4 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_14fc8 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_15028 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_15048 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_1505c P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_15078 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_15088 P with "Hlookup Hcode").
  iApply (write_success_transactions_chunk_150e8 P with
    "Hlookup Hcode Houtput").
  iApply (write_success_transactions_chunk_150f0 P with
    "Hlookup Hcode Hoptional").
  iApply (write_success_transactions_chunk_150fc P with
    "Hlookup Hcode Hint64").
  iApply (write_success_transactions_chunk_15108 P with
    "Hlookup Hcode Hint128").
  iApply (write_success_transactions_chunk_15118 P with
    "Hlookup Hcode Hboolean Hint128").
  iApply (write_success_transactions_chunk_15148 P with
    "Hlookup Hcode Hint64").
  iApply (write_success_transactions_chunk_15154 P with
    "Hlookup Hcode Hboolean Houtput").
  iExact "Hnext".
Qed.
