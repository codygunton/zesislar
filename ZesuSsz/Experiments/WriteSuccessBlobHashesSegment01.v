Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsHashesLoop HintsBlobHashesLoop HintsStorageKeysLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccess.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSegment01A.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSegment01B.

Lemma write_success_blob_hashes_chunk0a `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x153dc (writeSuccessBlobHashesLoopSpec P) -∗
  instr_body 0x153d4 (writeSuccessBlobHashesLoopSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iPoseProof (write_success_blob_hashes_chunk0a_153d8 P with
    "Hlookup Hcode Hnext") as "Hmiddle".
  iApply (write_success_blob_hashes_chunk0a_153d4 P with
    "Hlookup Hcode Hmiddle").
Qed.
