Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPayloadCall.

Import ListNotations.

Local Remove Hints
  InstrSpecs.Lookup.find_in_context_instr_body_lookup_resources_inst
  : typeclass_instances.

Ltac run_write_success_exact_header_tag afterTag :=
  lazymatch goal with
  | |- instr_body 0x14e14 _ => idtac
  | _ =>
      first
        [ progress iEval (unfold zesuWriteOutputPayloadCallSpec, zesu_c_call)
        | iExists (afterTag, tt)ₗ
        | liAStep
        | progress prepare_sidecond
        | reflexivity
        | vm_compute
        | bv_solve
        | lia ];
      run_write_success_exact_header_tag afterTag
  end.

Lemma write_success_exact_header_chunk_14e00
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (afterTag tail : spec)
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputPayloadCallSpec -∗
  instr_body 0x14e14
    (writeSuccessHeaderBeforeCopySpec sp bytes afterTag tail
      (bv_unsigned (BV 64 0x179c5) ↦ₘ∗
        writeSuccessPrivateBytes [90; 83; 83; 90; 1; 1] ∗ P)) -∗
  instr_body 0x14e00
    (writeSuccessHeaderBeforeCopySpec sp bytes
      (writeOutputEvents (BV 64 0x179c5) (BV 64 6)
        (writeSuccessPrivateBytes [90; 83; 83; 90; 1; 1]) afterTag)
      tail
      (bv_unsigned (BV 64 0x179c5) ↦ₘ∗
        writeSuccessPrivateBytes [90; 83; 83; 90; 1; 1] ∗ P)).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode #Houtput Hnext".
  run_write_success_exact_header_tag afterTag.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
Qed.

Print Assumptions write_success_exact_header_chunk_14e00.
