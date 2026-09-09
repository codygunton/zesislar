Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_90.a156a0.
Require Import IslaTraces.write_success_90.a156a4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0Defs.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0Existence.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0CoverageSuffix.

Lemma writeSuccess156a0ObservationsSplit regs global :
  writeSuccess156a0Observations regs global =
    writeSuccess156a0First5Observations regs global ++
    writeSuccess156a0CoverageTailObservations regs global.
Proof.
  unfold writeSuccess156a0Observations,
    writeSuccess156a0CoverageTailObservations.
  rewrite writeSuccess156a0PrefixObservationsSplit.
  rewrite app_assoc. reflexivity.
Qed.

Lemma segment_156a0_mstatus_covered (regs : reg_map) (global : seq_global_state)
    oldX1 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a0)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a0 = Some a156a0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a4 = Some a156a4 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156a0Before regs global)
    observations after ->
  after = writeSuccess156a0After regs global /\
  observations = writeSuccess156a0Observations regs global.
Proof.
  intros Hpc Hx1 Hcode Hnext Hmstatus Hsegment.
  destruct (segment_156a0_prefix5_covered regs global observations after
    Hpc Hmstatus Hsegment) as
    (done & labels & spawned & prefix5 & Hprefix5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_156a0_suffix_covered regs global oldX1
    prefix5 done labels spawned after Hpc Hx1 Hnext Hprefix5 Hnil Hdone)
    as (Hafter & Hsuffix).
  split; first exact Hafter.
  repeat rewrite <- app_assoc in Hobs. rewrite Hsuffix in Hobs.
  rewrite writeSuccess156a0ObservationsSplit. exact Hobs.
Qed.

Lemma segment_156a0_covered (regs : reg_map) (global : seq_global_state)
    oldX1 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a0)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a0 = Some a156a0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a4 = Some a156a4 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156a0Before regs global)
    observations after ->
  after = writeSuccess156a0After regs global /\
  observations = writeSuccess156a0Observations regs global.
Proof.
  intros Hpc Hx1 Hcode Hnext Hmstatus Hsegment.
  eapply segment_156a0_mstatus_covered; eauto.
Qed.

Print Assumptions writeSuccess156a0ObservationsSplit.
Print Assumptions segment_156a0_mstatus_covered.
Print Assumptions segment_156a0_covered.
