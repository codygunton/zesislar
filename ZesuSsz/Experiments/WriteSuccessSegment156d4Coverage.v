Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_94.a156d4.
Require Import IslaTraces.write_success_94.a156d8.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4CoverageSuffix.

Lemma writeSuccess156d4ObservationsSplit regs global :
  writeSuccess156d4Observations regs global =
  writeSuccess156d4First5Observations regs global ++
  writeSuccess156d4TailObservations regs global.
Proof.
  unfold writeSuccess156d4Observations,
    writeSuccess156d4First5Observations,
    writeSuccess156d4TailObservations,
    writeSuccess156d4PrefixObservations. cbn. reflexivity.
Qed.

Lemma segment_156d4_mstatus_covered regs global oldX1 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156d4)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156d4 = Some a156d4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156d8 = Some a156d8 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156d4Before regs global)
    observations after ->
  after = writeSuccess156d4After regs global /\
  observations = writeSuccess156d4Observations regs global.
Proof.
  intros Hpc Hdest Hcode Hnext Hmstatus Hsegment.
  destruct (segment_156d4_prefix5_covered regs global observations after
    Hpc Hmstatus Hsegment) as
    (done & labels & spawned & prefix5 & Hprefix5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_156d4_suffix_covered regs global oldX1
    prefix5 done labels spawned after Hpc Hdest Hnext Hprefix5 Hnil Hdone)
    as (Hafter & Hsuffix).
  split; first exact Hafter.
  repeat rewrite <- app_assoc in Hobs. rewrite Hsuffix in Hobs.
  rewrite writeSuccess156d4ObservationsSplit. exact Hobs.
Qed.

Lemma segment_156d4_covered regs global oldX1 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156d4)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156d4 = Some a156d4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156d8 = Some a156d8 ->
  writeSuccessTraceAssumptions (writeSuccess156d4Before regs global) ->
  IslaInstructionSegment (writeSuccess156d4Before regs global)
    observations after ->
  after = writeSuccess156d4After regs global /\
  observations = writeSuccess156d4Observations regs global.
Proof.
  intros Hpc Hdest Hcode Hnext Hassumptions Hsegment.
  eapply segment_156d4_mstatus_covered; eauto.
  exact (writeSuccess15694MstatusFromTraceAssumptions regs global Hassumptions).
Qed.

Print Assumptions writeSuccess156d4ObservationsSplit.
Print Assumptions segment_156d4_mstatus_covered.
Print Assumptions segment_156d4_covered.
