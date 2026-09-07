Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_93.a156c8.
Require Import IslaTraces.write_success_93.a156cc.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c8CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c8CoverageSuffix.

Lemma writeSuccess156c8ObservationsSplit regs global :
  writeSuccess156c8Observations regs global =
  writeSuccess156c8First5Observations regs global ++
  writeSuccess156c8TailObservations regs global.
Proof.
  unfold writeSuccess156c8Observations,
    writeSuccess156c8First5Observations,
    writeSuccess156c8TailObservations,
    writeSuccess156c8PrefixObservations. cbn. reflexivity.
Qed.

Lemma segment_156c8_mstatus_covered regs global oldX1 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c8)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156c8 = Some a156c8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156cc = Some a156cc ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156c8Before regs global)
    observations after ->
  after = writeSuccess156c8After regs global /\
  observations = writeSuccess156c8Observations regs global.
Proof.
  intros Hpc Hdest Hcode Hnext Hmstatus Hsegment.
  destruct (segment_156c8_prefix5_covered regs global observations after
    Hpc Hmstatus Hsegment) as
    (done & labels & spawned & prefix5 & Hprefix5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_156c8_suffix_covered regs global oldX1
    prefix5 done labels spawned after Hpc Hdest Hnext Hprefix5 Hnil Hdone)
    as (Hafter & Hsuffix).
  split; first exact Hafter.
  repeat rewrite <- app_assoc in Hobs. rewrite Hsuffix in Hobs.
  rewrite writeSuccess156c8ObservationsSplit. exact Hobs.
Qed.

Lemma segment_156c8_covered regs global oldX1 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c8)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156c8 = Some a156c8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156cc = Some a156cc ->
  writeSuccessTraceAssumptions (writeSuccess156c8Before regs global) ->
  IslaInstructionSegment (writeSuccess156c8Before regs global)
    observations after ->
  after = writeSuccess156c8After regs global /\
  observations = writeSuccess156c8Observations regs global.
Proof.
  intros Hpc Hdest Hcode Hnext Hassumptions Hsegment.
  eapply segment_156c8_mstatus_covered; eauto.
  exact (writeSuccess15694MstatusFromTraceAssumptions regs global Hassumptions).
Qed.

Print Assumptions writeSuccess156c8ObservationsSplit.
Print Assumptions segment_156c8_mstatus_covered.
Print Assumptions segment_156c8_covered.
