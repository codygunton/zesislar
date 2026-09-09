From Coq Require Import Lia Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessInstructionRunSplit.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f0.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyByteCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyByteRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyInduction.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Theorem writeSuccessMemcpyBytesRunCoveredWithRecords
    (regs : reg_map) (global : seq_global_state)
    (source destination index totalLength : bv 64) (bytes : list (bv 8))
    segments after :
  writeSuccessMemcpyBytesReady regs global source destination index totalLength
    bytes ->
  IslaInstructionRun (7 * List.length bytes)
    (writeSuccess101d8Before regs global) segments after ->
  after = writeSuccessMemcpyBytesAfter regs global source destination index bytes /\
  segmentRecords (writeSuccess101d8Before regs global)
    (flattenMicroObservations segments) = [].
Proof.
  revert regs global index segments after.
  induction bytes as [|byte tail IH]; intros regs global index segments after
    Hready Hrun.
  - cbn in Hrun. inversion Hrun; subst. split; reflexivity.
  - cbn in Hready |- *. destruct Hready as (Hhead & Htail).
    unfold writeSuccessMemcpyByteReady in Hhead.
    destruct Hhead as
      (Hpc & Hx10 & Hx11 & Hx12 & Hx15 & Hne & Htable & Hfacts & Hread &
       HsourceLower & HsourceUpper & HdestinationLower & HdestinationUpper &
       Hbacked).
    replace (7 * S (List.length tail))%nat with
      (7 + 7 * List.length tail)%nat in Hrun by lia.
    destruct (islaInstructionRun_split 7 (7 * List.length tail) _ _ _ Hrun) as
      (headSegments & middle & tailSegments & Hsegments & HheadRun & HtailRun).
    destruct (writeSuccessMemcpyByteRunCoveredWithRecords regs global source
      destination index totalLength byte headSegments middle Hpc Hx10 Hx11
      Hx12 Hx15 Hne Htable Hfacts Hread HsourceLower HsourceUpper
      HdestinationLower HdestinationUpper Hbacked HheadRun) as
      (Hmiddle & HheadRecords).
    subst middle.
    destruct (IH
      (writeSuccessMemcpyByteRegs regs source destination index byte)
      (writeSuccess101f0Global global
        (writeSuccessMemcpyDestinationAddress destination index)
        (writeSuccess101e4Loaded byte))
      (index + BV 64 1)%bv tailSegments after Htail HtailRun) as
      (Hafter & HtailRecords).
    split; first exact Hafter.
    subst segments.
    rewrite flattenMicroObservationsApp.
    rewrite (segmentRecords_app (writeSuccess101d8Before regs global)
      (flattenMicroObservations headSegments)
      (writeSuccessMemcpyByteAfter regs global source destination index byte)
      (flattenMicroObservations tailSegments)).
    + rewrite HheadRecords. rewrite HtailRecords. reflexivity.
    + exact (islaInstructionRunCorrespondence 7 _ _ _ HheadRun).
Qed.

Print Assumptions writeSuccessMemcpyBytesRunCoveredWithRecords.
