Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment17A.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment17B.

Lemma write_success_blob_hashes_chunk1e `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15494 (writeSuccessBlobHashesBodySpec P) -∗
  instr_body 0x1548c (writeSuccessBlobHashesBodySpec P).
Proof.
  iIntros "#Hlookup _ Hnext".
  iPoseProof (write_success_blob_hashes_segment17_b P with
    "Hlookup Hnext") as "Hmiddle".
  iApply (write_success_blob_hashes_segment17_a P with "Hlookup Hmiddle").
Qed.
