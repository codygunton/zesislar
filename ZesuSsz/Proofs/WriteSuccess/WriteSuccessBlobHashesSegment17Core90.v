Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import Index.
Require Import IslaTraces.write_success_67.a15490_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15Frame.

Local Remove Hints a15490_spec_inst : typeclass_instances.

Lemma write_success_blob_hashes_segment17_core_15490
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (byte : bv 8) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15494
    (writeSuccessBlobHashesLbuResult P "x22" 19 1 sp pointer base total
      processed remaining bytes tail byte) -∗
  instr_body 0x15490 (writeSuccessBlobHashesLbuState P "x22" 19 1 sp
    pointer base total processed remaining bytes tail byte).
Proof. move => *. zesu_block. Qed.
