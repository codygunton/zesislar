Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment02State.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment02ACore.

Lemma write_success_blob_hashes_chunk0b_153dc `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x153e0 (writeSuccessBlobHashesLoopSpec P) -∗
  instr_body 0x153dc (writeSuccessBlobHashesLoopSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  rewrite /writeSuccessBlobHashesLoopSpec.
  iDestruct "Hentry" as
    (sp pointer base total processed remaining bytes tail) "Hstate".
  iPoseProof (write_success_blob_hashes_chunk0b_153dc_core P sp pointer base
    total processed remaining bytes tail with "Hlookup Hcode Hnext")
    as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody".
  iExact "Hstate".
Qed.
