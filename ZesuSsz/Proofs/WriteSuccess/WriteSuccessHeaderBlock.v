From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.
Require Import ZesuSsz.Experiments.WriteSuccessHeaderSpec.
Require Import ZesuSsz.Experiments.WriteSuccessHeaderChunk14e00.
Require Import ZesuSsz.Experiments.WriteSuccessHeaderChunk14e14.
Require Import ZesuSsz.Experiments.WriteSuccessHeaderChunk14e28.
Require Import ZesuSsz.Experiments.WriteSuccessHeaderChunk14e38.
Require Import ZesuSsz.Experiments.WriteSuccessHeaderChunk14e48.
Require Import ZesuSsz.Experiments.WriteSuccessHeaderChunk14e58.
Require Import ZesuSsz.Experiments.WriteSuccessHeaderChunk14e68.
Require Import ZesuSsz.Experiments.WriteSuccessHeaderChunk14e78.

Import ListNotations.

Lemma write_success_header_block `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_body 0x14e00 (writeSuccessHeaderSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hmemcpy #Houtput".
  iAssert (□ instr_pre 0x101d4 zesuMemcpyCallSpec)%I with "[]"
    as "HmemcpyBox".
  { iModIntro. iExact "Hmemcpy". }
  iAssert (□ instr_pre 0x10190 zesuWriteOutputCallSpec)%I with "[]"
    as "HoutputBox".
  { iModIntro. iExact "Houtput". }
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessHeaderSpec.
  iDestruct "Hentry" as (sp bytes tail) "Hentry".
  iAssert (instr_body 0x14e78
      (writeSuccessHeaderAfterCopySpec sp bytes
        (writeSuccessHeaderEventsAfter1300 sp tail) tail P)) as "H78".
  { iApply (write_success_header_chunk_14e78 sp bytes tail P with
      "Hlookup Hcode").
    rewrite instr_pre'_eq.
    iExact "HoutputBox". }
  iAssert (instr_body 0x14e68
      (writeSuccessHeaderAfterCopySpec sp bytes
        (writeSuccessHeaderEventsAfter1268 sp tail) tail P)) as "H68".
  { iApply (write_success_header_chunk_14e68 sp bytes tail P with
      "Hlookup Hcode").
    - rewrite instr_pre'_eq. iExact "HoutputBox".
    - iExact "H78". }
  iAssert (instr_body 0x14e58
      (writeSuccessHeaderAfterCopySpec sp bytes
        (writeSuccessHeaderEventsAfter1236 sp tail) tail P)) as "H58".
  { iApply (write_success_header_chunk_14e58 sp bytes tail P with
      "Hlookup Hcode").
    - rewrite instr_pre'_eq. iExact "HoutputBox".
    - iExact "H68". }
  iAssert (instr_body 0x14e48
      (writeSuccessHeaderAfterCopySpec sp bytes
        (writeSuccessHeaderEventsAfter1216 sp tail) tail P)) as "H48".
  { iApply (write_success_header_chunk_14e48 sp bytes tail P with
      "Hlookup Hcode").
    - rewrite instr_pre'_eq. iExact "HoutputBox".
    - iExact "H58". }
  iAssert (instr_body 0x14e38
      (writeSuccessHeaderAfterCopySpec sp bytes
        (writeSuccessHeaderEventsAfter1184 sp tail) tail P)) as "H38".
  { iApply (write_success_header_chunk_14e38 sp bytes tail P with
      "Hlookup Hcode").
    - rewrite instr_pre'_eq. iExact "HoutputBox".
    - iExact "H48". }
  iAssert (instr_body 0x14e28
      (writeSuccessHeaderAfterCopySpec sp bytes
        (writeSuccessHeaderEventsAfterTag sp tail) tail P)) as "H28".
  { iApply (write_success_header_chunk_14e28 sp bytes tail P with
      "Hlookup Hcode").
    - rewrite instr_pre'_eq. iExact "HoutputBox".
    - iExact "H38". }
  iAssert (instr_body 0x14e14
      (writeSuccessHeaderBeforeCopySpec sp bytes
        (writeSuccessHeaderEventsAfterTag sp tail) tail P)) as "H14".
  { iApply (write_success_header_chunk_14e14 sp bytes tail P with
      "Hlookup Hcode").
    - rewrite instr_pre'_eq. iExact "HmemcpyBox".
    - iExact "H28". }
  iAssert (instr_body 0x14e00
      (writeSuccessHeaderBeforeCopySpec sp bytes
        (writeSuccessHeaderEvents sp tail) tail P)) as "H00".
  { iApply (write_success_header_chunk_14e00 sp bytes tail P with
      "Hlookup Hcode").
    - rewrite instr_pre'_eq. iExact "HoutputBox".
    - iExact "H14". }
  iEval (rewrite instr_pre'_eq) in "H00".
  iApply "H00". iExact "Hentry".
Qed.
