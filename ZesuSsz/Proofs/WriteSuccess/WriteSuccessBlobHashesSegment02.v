Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSegment02A.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSegment02B.

Lemma write_success_blob_hashes_chunk0b `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x153e4 (writeSuccessBlobHashesLoopSpec P) -∗
  instr_body 0x153dc (writeSuccessBlobHashesLoopSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iPoseProof (write_success_blob_hashes_chunk0b_153e0 P with
    "Hlookup Hcode Hnext") as "Hmiddle".
  iApply (write_success_blob_hashes_chunk0b_153dc P with
    "Hlookup Hcode Hmiddle").
Qed.
