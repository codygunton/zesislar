Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import Index.
Require Import IslaTraces.write_success_68.a15494_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15Frame.

Local Remove Hints a15494_spec_inst : typeclass_instances.

Lemma write_success_blob_hashes_chunk2a_raw_15494
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (byte : bv 8) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15498
    (writeSuccessBlobHashesLbuResult P "x23" 20 2 sp pointer base total
      processed remaining bytes tail byte) -∗
  instr_body 0x15494
    (writeSuccessBlobHashesLbuState P "x23" 20 2 sp pointer base total
      processed remaining bytes tail byte).
Proof. move => *. zesu_block. Qed.
