Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith.ZArith.
From stdpp Require Import gmap.
Require Import isla.opsem.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Generated.ApprovedProgram.

Record AdmissibleProgram : Type := {
  programInstructions : gmap addr isla_trace;
  programApproved : approvedProgram ⊆ programInstructions;
  programDecoderCode : forall pc,
    PcInRanges decodeInputExecutionPcRanges pc ->
    (pc mod 4 = 0)%Z ->
    exists trace, programInstructions !! Z_to_bv 64 pc = Some trace
}.

Lemma approved_program_no_shadow (P : AdmissibleProgram) address trace :
  approvedProgram !! address = Some trace ->
  programInstructions P !! address = Some trace.
Proof.
  exact (proj1 (map_subseteq_spec approvedProgram (programInstructions P))
    (programApproved P) address trace).
Qed.

Print Assumptions approved_program_no_shadow.
