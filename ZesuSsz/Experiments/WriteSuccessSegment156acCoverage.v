Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_91.a156ac.
Require Import IslaTraces.write_success_91.a156b0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156ac.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156acCoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156acCoverageSuffix.

Lemma writeSuccess156acObservationsSplit regs global :
  writeSuccess156acObservations regs global =
  writeSuccess156acFirst5Observations regs global ++
  writeSuccess156acTailObservations regs global.
Proof.
  unfold writeSuccess156acObservations,
    writeSuccess156acFirst5Observations,
    writeSuccess156acTailObservations,
    writeSuccess156acPrefixObservations. cbn. reflexivity.
Qed.

Lemma segment_156ac_mstatus_covered regs global oldX1 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156ac)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156ac = Some a156ac ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b0 = Some a156b0 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156acBefore regs global)
    observations after ->
  after = writeSuccess156acAfter regs global /\
  observations = writeSuccess156acObservations regs global.
Proof.
  intros Hpc Hdest Hcode Hnext Hmstatus Hsegment.
  destruct (segment_156ac_prefix5_covered regs global observations after
    Hpc Hmstatus Hsegment) as
    (done & labels & spawned & prefix5 & Hprefix5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_156ac_suffix_covered regs global oldX1
    prefix5 done labels spawned after Hpc Hdest Hnext Hprefix5 Hnil Hdone)
    as (Hafter & Hsuffix).
  split; first exact Hafter.
  repeat rewrite <- app_assoc in Hobs. rewrite Hsuffix in Hobs.
  rewrite writeSuccess156acObservationsSplit. exact Hobs.
Qed.

Lemma segment_156ac_covered regs global oldX1 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156ac)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156ac = Some a156ac ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b0 = Some a156b0 ->
  writeSuccessTraceAssumptions (writeSuccess156acBefore regs global) ->
  IslaInstructionSegment (writeSuccess156acBefore regs global)
    observations after ->
  after = writeSuccess156acAfter regs global /\
  observations = writeSuccess156acObservations regs global.
Proof.
  intros Hpc Hdest Hcode Hnext Hassumptions Hsegment.
  eapply segment_156ac_mstatus_covered; eauto.
  exact (writeSuccess15694MstatusFromTraceAssumptions regs global Hassumptions).
Qed.

Print Assumptions writeSuccess156acObservationsSplit.
Print Assumptions segment_156ac_mstatus_covered.
Print Assumptions segment_156ac_covered.
