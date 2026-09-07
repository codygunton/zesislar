Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101e0.
Require Import IslaTraces.write_success_02.a101e4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e0CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e0CoverageSuffix.

Lemma writeSuccess101e0ObservationsSplit regs global left right :
  writeSuccess101e0Observations regs global left right =
  writeSuccess101e0First7Observations regs global left ++
  writeSuccess101e0TailObservations regs global left right.
Proof.
  unfold writeSuccess101e0Observations,
    writeSuccess101e0First7Observations,
    writeSuccess101e0TailObservations,
    writeSuccess101e0PrefixObservations,
    writeSuccess101e0Locals. cbn. reflexivity.
Qed.

Lemma segment_101e0_mstatus_covered regs global (left right : bv 64) oldX13
    observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e0)) ->
  regs !! "x11" = Some (RVal_Bits left) ->
  regs !! "x15" = Some (RVal_Bits right) ->
  regs !! "x13" = Some oldX13 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e0 = Some a101e0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e4 = Some a101e4 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101e0Before regs global)
    observations after ->
  after = writeSuccess101e0After regs global left right /\
  observations = writeSuccess101e0Observations regs global left right.
Proof.
  intros Hpc Hleft Hright Hdest Hcode Hnext Hmstatus Hsegment.
  destruct (segment_101e0_prefix7_covered regs global left observations after
    Hpc Hleft Hmstatus Hsegment) as
    (done & labels & spawned & prefix7 & Hprefix7 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_101e0_suffix_covered regs global left right oldX13
    prefix7 done labels spawned after Hpc Hright Hdest Hnext Hprefix7 Hnil Hdone)
    as (Hafter & Hsuffix).
  split; first exact Hafter.
  repeat rewrite <- app_assoc in Hobs. rewrite Hsuffix in Hobs.
  rewrite writeSuccess101e0ObservationsSplit. exact Hobs.
Qed.

Lemma segment_101e0_covered regs global (left right : bv 64) oldX13
    observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e0)) ->
  regs !! "x11" = Some (RVal_Bits left) ->
  regs !! "x15" = Some (RVal_Bits right) ->
  regs !! "x13" = Some oldX13 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e0 = Some a101e0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e4 = Some a101e4 ->
  writeSuccessTraceAssumptions (writeSuccess101e0Before regs global) ->
  IslaInstructionSegment (writeSuccess101e0Before regs global)
    observations after ->
  after = writeSuccess101e0After regs global left right /\
  observations = writeSuccess101e0Observations regs global left right.
Proof.
  intros Hpc Hleft Hright Hdest Hcode Hnext Hassumptions Hsegment.
  eapply segment_101e0_mstatus_covered; eauto.
  exact (writeSuccess15694MstatusFromTraceAssumptions regs global Hassumptions).
Qed.

Print Assumptions writeSuccess101e0ObservationsSplit.
Print Assumptions segment_101e0_mstatus_covered.
Print Assumptions segment_101e0_covered.
