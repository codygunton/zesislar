Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSegment17A.

Lemma write_success_blob_hashes_segment17_lbu_raw
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15490 (writeSuccessBlobHashesBodySpec P) -∗
  instr_body 0x1548c (writeSuccessBlobHashesBodySpec P).
Proof.
  iIntros "#Hlookup _ Hnext".
  iApply (write_success_blob_hashes_segment17_a P with "Hlookup Hnext").
Qed.
