Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment14ACompose.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment14BCompose.

Lemma write_success_blob_hashes_chunk1b `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x1545c (writeSuccessBlobHashesBodySpec P) -∗
  instr_body 0x15454 (writeSuccessBlobHashesBodySpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iPoseProof (write_success_blob_hashes_segment14b P with
    "Hlookup Hcode Hnext") as "Hnext".
  iApply (write_success_blob_hashes_segment14a P with
    "Hlookup Hcode Hnext").
Qed.
