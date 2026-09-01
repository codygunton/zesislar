From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsHashesLoop HintsBlobHashesLoop HintsStorageKeysLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccess.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesChunk2A.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesChunk2B.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesChunk2C.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesChunk2D.
#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma write_success_blob_hashes_chunk2 `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x154f4 (writeSuccessBlobHashesBodySpec P) -∗
  instr_body 0x15494 (writeSuccessBlobHashesBodySpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode Hnext".
  iApply (write_success_blob_hashes_chunk2a P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk2b P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk2c P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk2d P with "Hlookup Hcode").
  iExact "Hnext".
Qed.
