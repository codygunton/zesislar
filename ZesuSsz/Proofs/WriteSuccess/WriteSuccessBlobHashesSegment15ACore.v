Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import Index.
Require Import IslaTraces.write_success_67.a1545c_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15Frame.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15AReturn.

Local Remove Hints a1545c_spec_inst : typeclass_instances.
Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma write_success_blob_hashes_segment15a_core
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (byte : bv 8) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15460
    (writeSuccessBlobHashesLbuResult P "x18" 16 10 sp pointer base total
      processed remaining bytes tail byte) -∗
  instr_body 0x1545c (writeSuccessBlobHashesLbuState P "x18" 16 10 sp
    pointer base total processed remaining bytes tail byte).
Proof. move => *. zesu_block. Qed.
