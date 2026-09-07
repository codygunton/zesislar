Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101e8.
Require Import IslaTraces.write_success_02.a101ec.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e8CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e8CoverageSuffix.

Lemma writeSuccess101e8ObservationsSplit regs global left right :
  writeSuccess101e8Observations regs global left right =
  writeSuccess101e8First7Observations regs global left ++
  writeSuccess101e8TailObservations regs global left right.
Proof.
  unfold writeSuccess101e8Observations,
    writeSuccess101e8First7Observations,
    writeSuccess101e8TailObservations,
    writeSuccess101e8PrefixObservations,
    writeSuccess101e8Locals. cbn. reflexivity.
Qed.

Lemma segment_101e8_mstatus_covered regs global (left right : bv 64) oldX14
    observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e8)) ->
  regs !! "x10" = Some (RVal_Bits left) ->
  regs !! "x15" = Some (RVal_Bits right) ->
  regs !! "x14" = Some oldX14 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e8 = Some a101e8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101ec = Some a101ec ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101e8Before regs global)
    observations after ->
  after = writeSuccess101e8After regs global left right /\
  observations = writeSuccess101e8Observations regs global left right.
Proof.
  intros Hpc Hleft Hright Hdest Hcode Hnext Hmstatus Hsegment.
  destruct (segment_101e8_prefix7_covered regs global left observations after
    Hpc Hleft Hmstatus Hsegment) as
    (done & labels & spawned & prefix7 & Hprefix7 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_101e8_suffix_covered regs global left right oldX14
    prefix7 done labels spawned after Hpc Hright Hdest Hnext Hprefix7 Hnil Hdone)
    as (Hafter & Hsuffix).
  split; first exact Hafter.
  repeat rewrite <- app_assoc in Hobs. rewrite Hsuffix in Hobs.
  rewrite writeSuccess101e8ObservationsSplit. exact Hobs.
Qed.

Lemma segment_101e8_covered regs global (left right : bv 64) oldX14
    observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e8)) ->
  regs !! "x10" = Some (RVal_Bits left) ->
  regs !! "x15" = Some (RVal_Bits right) ->
  regs !! "x14" = Some oldX14 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e8 = Some a101e8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101ec = Some a101ec ->
  writeSuccessTraceAssumptions (writeSuccess101e8Before regs global) ->
  IslaInstructionSegment (writeSuccess101e8Before regs global)
    observations after ->
  after = writeSuccess101e8After regs global left right /\
  observations = writeSuccess101e8Observations regs global left right.
Proof.
  intros Hpc Hleft Hright Hdest Hcode Hnext Hassumptions Hsegment.
  eapply segment_101e8_mstatus_covered; eauto.
  exact (writeSuccess15694MstatusFromTraceAssumptions regs global Hassumptions).
Qed.

Print Assumptions writeSuccess101e8ObservationsSplit.
Print Assumptions segment_101e8_mstatus_covered.
Print Assumptions segment_101e8_covered.
