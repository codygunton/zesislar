Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactHeaderCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactHeaderChunk14e00.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactHeaderChunk14e14.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactHeaderChunk14e28.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactHeaderChunk14e78.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactHeaderSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPayloadCall.

Import ListNotations.

Lemma write_success_exact_header_block `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputPayloadCallSpec -∗
  instr_body 0x14e00 (writeSuccessExactHeaderSpec P).
Proof.
  move => *. iStartProof. iIntros "_ #Hlookup #Hcode #Hmemcpy #Houtput".
  iAssert (□ instr_pre 0x101d4 zesuMemcpyCallSpec)%I with "[]" as "HmemcpyBox".
  { iModIntro. iExact "Hmemcpy". }
  iAssert (□ instr_pre 0x10190 zesuWriteOutputPayloadCallSpec)%I with "[]" as "HoutputBox".
  { iModIntro. iExact "Houtput". }
  rewrite instr_pre'_eq. iIntros "Hentry". rewrite /writeSuccessExactHeaderSpec.
  iDestruct "Hentry" as (sp bytes tail) "Hentry".
  set (Q := (bv_unsigned (BV 64 0x179c5) ↦ₘ∗ writeSuccessPrivateBytes [90; 83; 83; 90; 1; 1] ∗ P)%I).
  iAssert (instr_body 0x14e78 (writeSuccessHeaderAfterCopySpec sp bytes (writeSuccessExactHeaderEventsAfter1300 sp bytes tail) tail Q)) as "H78".
  { iApply (write_success_exact_header_chunk_14e78 sp bytes tail Q with "Hlookup Hcode"). rewrite instr_pre'_eq. iExact "HoutputBox". }
  iAssert (instr_body 0x14e68 (writeSuccessHeaderAfterCopySpec sp bytes (writeSuccessExactHeaderEventsAfter1268 sp bytes tail) tail Q)) as "H68".
  { iApply (write_success_exact_header_chunk_14e68 sp bytes tail Q with "Hlookup Hcode"); [rewrite instr_pre'_eq; iExact "HoutputBox" | iExact "H78"]. }
  iAssert (instr_body 0x14e58 (writeSuccessHeaderAfterCopySpec sp bytes (writeSuccessExactHeaderEventsAfter1236 sp bytes tail) tail Q)) as "H58".
  { iApply (write_success_exact_header_chunk_14e58 sp bytes tail Q with "Hlookup Hcode"); [rewrite instr_pre'_eq; iExact "HoutputBox" | iExact "H68"]. }
  iAssert (instr_body 0x14e48 (writeSuccessHeaderAfterCopySpec sp bytes (writeSuccessExactHeaderEventsAfter1216 sp bytes tail) tail Q)) as "H48".
  { iApply (write_success_exact_header_chunk_14e48 sp bytes tail Q with "Hlookup Hcode"); [rewrite instr_pre'_eq; iExact "HoutputBox" | iExact "H58"]. }
  iAssert (instr_body 0x14e38 (writeSuccessHeaderAfterCopySpec sp bytes (writeSuccessExactHeaderEventsAfter1184 sp bytes tail) tail Q)) as "H38".
  { iApply (write_success_exact_header_chunk_14e38 sp bytes tail Q with "Hlookup Hcode"); [rewrite instr_pre'_eq; iExact "HoutputBox" | iExact "H48"]. }
  iAssert (instr_body 0x14e28 (writeSuccessHeaderAfterCopySpec sp bytes (writeSuccessExactHeaderEventsAfterTag sp bytes tail) tail Q)) as "H28".
  { iApply (write_success_exact_header_chunk_14e28 sp bytes tail Q with "Hlookup Hcode"); [rewrite instr_pre'_eq; iExact "HoutputBox" | iExact "H38"]. }
  iAssert (instr_body 0x14e14 (writeSuccessHeaderBeforeCopySpec sp bytes (writeSuccessExactHeaderEventsAfterTag sp bytes tail) tail Q)) as "H14".
  { iApply (write_success_exact_header_chunk_14e14 sp bytes tail Q with "Hlookup Hcode"); [rewrite instr_pre'_eq; iExact "HmemcpyBox" | iExact "H28"]. }
  iAssert (instr_body 0x14e00 (writeSuccessHeaderBeforeCopySpec sp bytes (writeSuccessExactHeaderEvents sp bytes tail) tail Q)) as "H00".
  { rewrite /writeSuccessExactHeaderEvents.
    iApply (write_success_exact_header_chunk_14e00 sp bytes
      (writeSuccessExactHeaderEventsAfterTag sp bytes tail) tail P with
      "Hlookup Hcode").
    - rewrite instr_pre'_eq. iExact "HoutputBox".
    - subst Q. iExact "H14". }
  iEval (rewrite instr_pre'_eq) in "H00".
  subst Q. iApply "H00". iExact "Hentry".
Qed.

Print Assumptions write_success_exact_header_block.
