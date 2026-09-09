Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_01.a10190.
Require Import IslaTraces.write_success_01.a10194.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190CoverageSuffix.

Lemma writeSuccess10190ObservationsSplit regs global :
  writeSuccess10190Observations regs global =
  writeSuccess10190First5Observations regs global ++
  writeSuccess10190TailObservations regs global.
Proof.
  unfold writeSuccess10190Observations,
    writeSuccess10190First5Observations,
    writeSuccess10190TailObservations,
    writeSuccess10190PrefixObservations. cbn. reflexivity.
Qed.

Lemma segment_10190_mstatus_covered regs global oldX5 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10190)) ->
  regs !! "x5" = Some oldX5 ->
  global.(seq_instrs) !! Z_to_bv 64 0x10190 = Some a10190 ->
  global.(seq_instrs) !! Z_to_bv 64 0x10194 = Some a10194 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess10190Before regs global)
    observations after ->
  after = writeSuccess10190After regs global /\
  observations = writeSuccess10190Observations regs global.
Proof.
  intros Hpc Hdest Hcode Hnext Hmstatus Hsegment.
  destruct (segment_10190_prefix5_covered regs global observations after
    Hpc Hmstatus Hsegment) as
    (done & labels & spawned & prefix5 & Hprefix5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_10190_suffix_covered regs global oldX5
    prefix5 done labels spawned after Hpc Hdest Hnext Hprefix5 Hnil Hdone)
    as (Hafter & Hsuffix).
  split; first exact Hafter.
  repeat rewrite <- app_assoc in Hobs. rewrite Hsuffix in Hobs.
  rewrite writeSuccess10190ObservationsSplit. exact Hobs.
Qed.

Lemma segment_10190_covered regs global oldX5 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10190)) ->
  regs !! "x5" = Some oldX5 ->
  global.(seq_instrs) !! Z_to_bv 64 0x10190 = Some a10190 ->
  global.(seq_instrs) !! Z_to_bv 64 0x10194 = Some a10194 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess10190Before regs global)
    observations after ->
  after = writeSuccess10190After regs global /\
  observations = writeSuccess10190Observations regs global.
Proof.
  intros Hpc Hdest Hcode Hnext Hmstatus Hsegment.
  eapply segment_10190_mstatus_covered; eauto.
Qed.

Print Assumptions writeSuccess10190ObservationsSplit.
Print Assumptions segment_10190_mstatus_covered.
Print Assumptions segment_10190_covered.
