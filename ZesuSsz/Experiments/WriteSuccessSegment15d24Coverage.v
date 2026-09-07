Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d24.
Require Import IslaTraces.write_success_07.a15d28.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d24.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d24CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d24CoverageSuffix.

Lemma writeSuccess15d24ObservationsSplit regs global :
  writeSuccess15d24Observations regs global =
  writeSuccess15d24First5Observations regs global ++
  writeSuccess15d24TailObservations regs global.
Proof.
  unfold writeSuccess15d24Observations,
    writeSuccess15d24First5Observations,
    writeSuccess15d24TailObservations,
    writeSuccess15d24PrefixObservations. cbn. reflexivity.
Qed.

Lemma segment_15d24_mstatus_covered regs global oldX1 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d24)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d24 = Some a15d24 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d28 = Some a15d28 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d24Before regs global)
    observations after ->
  after = writeSuccess15d24After regs global /\
  observations = writeSuccess15d24Observations regs global.
Proof.
  intros Hpc Hdest Hcode Hnext Hmstatus Hsegment.
  destruct (segment_15d24_prefix5_covered regs global observations after
    Hpc Hmstatus Hsegment) as
    (done & labels & spawned & prefix5 & Hprefix5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_15d24_suffix_covered regs global oldX1
    prefix5 done labels spawned after Hpc Hdest Hnext Hprefix5 Hnil Hdone)
    as (Hafter & Hsuffix).
  split; first exact Hafter.
  repeat rewrite <- app_assoc in Hobs. rewrite Hsuffix in Hobs.
  rewrite writeSuccess15d24ObservationsSplit. exact Hobs.
Qed.

Lemma segment_15d24_covered regs global oldX1 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d24)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d24 = Some a15d24 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d28 = Some a15d28 ->
  writeSuccessTraceAssumptions (writeSuccess15d24Before regs global) ->
  IslaInstructionSegment (writeSuccess15d24Before regs global)
    observations after ->
  after = writeSuccess15d24After regs global /\
  observations = writeSuccess15d24Observations regs global.
Proof.
  intros Hpc Hdest Hcode Hnext Hassumptions Hsegment.
  eapply segment_15d24_mstatus_covered; eauto.
  exact (writeSuccess15694MstatusFromTraceAssumptions regs global Hassumptions).
Qed.

Print Assumptions writeSuccess15d24ObservationsSplit.
Print Assumptions segment_15d24_mstatus_covered.
Print Assumptions segment_15d24_covered.
