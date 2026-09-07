Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_92.a156b8.
Require Import IslaTraces.write_success_92.a156bc.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b8CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b8CoverageSuffix.

Lemma writeSuccess156b8ObservationsSplit regs global :
  writeSuccess156b8Observations regs global =
  writeSuccess156b8First5Observations regs global ++
  writeSuccess156b8TailObservations regs global.
Proof.
  unfold writeSuccess156b8Observations,
    writeSuccess156b8First5Observations,
    writeSuccess156b8TailObservations,
    writeSuccess156b8PrefixObservations. cbn. reflexivity.
Qed.

Lemma segment_156b8_mstatus_covered regs global oldX1 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b8)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b8 = Some a156b8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156bc = Some a156bc ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156b8Before regs global)
    observations after ->
  after = writeSuccess156b8After regs global /\
  observations = writeSuccess156b8Observations regs global.
Proof.
  intros Hpc Hdest Hcode Hnext Hmstatus Hsegment.
  destruct (segment_156b8_prefix5_covered regs global observations after
    Hpc Hmstatus Hsegment) as
    (done & labels & spawned & prefix5 & Hprefix5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_156b8_suffix_covered regs global oldX1
    prefix5 done labels spawned after Hpc Hdest Hnext Hprefix5 Hnil Hdone)
    as (Hafter & Hsuffix).
  split; first exact Hafter.
  repeat rewrite <- app_assoc in Hobs. rewrite Hsuffix in Hobs.
  rewrite writeSuccess156b8ObservationsSplit. exact Hobs.
Qed.

Lemma segment_156b8_covered regs global oldX1 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b8)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b8 = Some a156b8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156bc = Some a156bc ->
  writeSuccessTraceAssumptions (writeSuccess156b8Before regs global) ->
  IslaInstructionSegment (writeSuccess156b8Before regs global)
    observations after ->
  after = writeSuccess156b8After regs global /\
  observations = writeSuccess156b8Observations regs global.
Proof.
  intros Hpc Hdest Hcode Hnext Hassumptions Hsegment.
  eapply segment_156b8_mstatus_covered; eauto.
  exact (writeSuccess15694MstatusFromTraceAssumptions regs global Hassumptions).
Qed.

Print Assumptions writeSuccess156b8ObservationsSplit.
Print Assumptions segment_156b8_mstatus_covered.
Print Assumptions segment_156b8_covered.
