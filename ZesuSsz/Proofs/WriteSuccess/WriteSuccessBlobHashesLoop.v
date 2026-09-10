From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsHashesLoop HintsBlobHashesLoop HintsStorageKeysLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccess.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment01.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment02.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment03.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment04.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment05.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment06.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment07.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment08.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment09.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment10.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment11.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment12.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment13.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment14.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment16.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment17.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment18.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment19.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment20.
#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma write_success_blob_hashes_chunk0 `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15434 (writeSuccessBlobHashesBodySpec P) -∗
  instr_body 0x153d4 (writeSuccessBlobHashesLoopSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode Hnext".
  iApply (write_success_blob_hashes_chunk0a P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0b P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0c P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0d P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0e P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0f P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0g P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0h P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0i P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0j P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0k P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0l P with "Hlookup Hcode").
  iExact "Hnext".
Qed.
Lemma write_success_blob_hashes_chunk1 `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15494 (writeSuccessBlobHashesBodySpec P) -∗
  instr_body 0x15434 (writeSuccessBlobHashesBodySpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode Hnext".
  iApply (write_success_blob_hashes_chunk1a P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk1b P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk1c P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk1d P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk1e P with "Hlookup Hcode").
  iExact "Hnext".
Qed.
Lemma write_success_blob_hashes_loop `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x153d4 (writeSuccessBlobHashesLoopSpec P) -∗
  instr_body 0x153d4 (writeSuccessBlobHashesLoopSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Houtput #Hloop".
  iApply (write_success_blob_hashes_chunk0 P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk1 P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk2 P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk3 P with
    "Hlookup Hcode Houtput").
  iApply (write_success_blob_hashes_tail P with
    "Hlookup Hcode Houtput Hloop").
Qed.
Lemma write_success_blob_hashes_loop_pre `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x153d4 (writeSuccessBlobHashesLoopSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Houtput".
  iLöb as "IH".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (write_success_blob_hashes_loop P with
    "Hlookup Hcode Houtput IH").
Qed.
