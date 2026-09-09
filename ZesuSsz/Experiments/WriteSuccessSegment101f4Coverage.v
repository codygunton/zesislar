Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101d8.
Require Import IslaTraces.write_success_02.a101f4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f4CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f4CoverageSuffix.

Lemma writeSuccess101f4ObservationsSplit regs global :
  writeSuccess101f4Observations regs global =
  writeSuccess101f4First5Observations regs global ++
  writeSuccess101f4TailObservations regs global.
Proof.
  unfold writeSuccess101f4Observations,
    writeSuccess101f4First5Observations,
    writeSuccess101f4TailObservations,
    writeSuccess101f4PrefixObservations. cbn. reflexivity.
Qed.

Lemma segment_101f4_mstatus_covered regs global observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101f4)) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101f4 = Some a101f4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101f4Before regs global)
    observations after ->
  after = writeSuccess101f4After regs global /\
  observations = writeSuccess101f4Observations regs global.
Proof.
  intros Hpc Hcode Hnext Hmstatus Hsegment.
  destruct (segment_101f4_prefix5_covered regs global observations after
    Hpc Hmstatus Hsegment) as
    (done & labels & spawned & prefix5 & Hprefix5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_101f4_suffix_covered regs global prefix5 done labels
    spawned after Hpc Hnext Hprefix5 Hnil Hdone) as (Hafter & Hsuffix).
  split; first exact Hafter.
  repeat rewrite <- app_assoc in Hobs. rewrite Hsuffix in Hobs.
  rewrite writeSuccess101f4ObservationsSplit. exact Hobs.
Qed.

Lemma segment_101f4_covered regs global observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101f4)) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101f4 = Some a101f4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101f4Before regs global)
    observations after ->
  after = writeSuccess101f4After regs global /\
  observations = writeSuccess101f4Observations regs global.
Proof.
  intros Hpc Hcode Hnext Hmstatus Hsegment.
  eapply segment_101f4_mstatus_covered; eauto.
Qed.

Print Assumptions writeSuccess101f4ObservationsSplit.
Print Assumptions segment_101f4_mstatus_covered.
Print Assumptions segment_101f4_covered.
