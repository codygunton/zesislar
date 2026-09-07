Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101d8.
Require Import IslaTraces.write_success_02.a101dc.
Require Import IslaTraces.write_success_02.a101e0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8CoveragePrefix6.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8CoveragePrefix12.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8CoverageTaken.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8CoverageFallthrough.

Lemma writeSuccess101d8CommonObservationsSplit left right condition regs global :
  writeSuccess101d8CommonObservations left right condition regs global =
  writeSuccess101d8First6Observations condition regs global ++
  writeSuccess101d8Second6Observations left right condition regs global.
Proof.
  unfold writeSuccess101d8First6Observations,
    writeSuccess101d8Second6Observations,
    writeSuccess101d8CommonObservations, writeSuccess101d8CommonLocals.
  cbn. reflexivity.
Qed.

Lemma segment_101d8_mstatus_covered regs global (left right : bv 64)
    observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  regs !! "x15" = Some (RVal_Bits left) ->
  regs !! "x12" = Some (RVal_Bits right) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101dc = Some a101dc ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e0 = Some a101e0 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101d8Before regs global)
    observations after ->
  after = writeSuccess101d8After left right regs global /\
  observations = writeSuccess101d8Observations left right regs global.
Proof.
  intros Hpc Hx15 Hx12 Hcode Hfall Htaken Hmstatus Hsegment.
  unfold writeSuccess101d8After, writeSuccess101d8Observations.
  destruct (decide (left = right)) as [Heq|Hne].
  - have Hcondition := writeSuccess101d8ConditionFallthrough left right Heq.
    destruct (segment_101d8_prefix6_covered regs global left right false
      observations after Hpc Hmstatus Hsegment) as
      (done & labels & spawned & prefix6 & Hprefix6 & Hnil & Hdone & Hend & Hobs).
    have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
    destruct (segment_101d8_prefix12_covered regs global left right false
      prefix6 done Hx15 Hx12 Hcondition Hprefix6 Hnil HdoneNb) as
      (prefix12 & Hprefix12 & Hsecond).
    destruct (segment_101d8_fallthrough_suffix_covered regs global left right
      prefix12 done labels spawned after Hpc Hfall Hprefix12 Hnil Hdone) as
      (Hafter & Hsuffix).
    split; first exact Hafter.
    rewrite Hsecond in Hobs. repeat rewrite <- app_assoc in Hobs.
    rewrite Hsuffix in Hobs.
    unfold writeSuccess101d8FallthroughAllObservations.
    rewrite writeSuccess101d8CommonObservationsSplit.
    rewrite app_assoc. exact Hobs.
  - have Hcondition := writeSuccess101d8ConditionTaken left right Hne.
    destruct (segment_101d8_prefix6_covered regs global left right true
      observations after Hpc Hmstatus Hsegment) as
      (done & labels & spawned & prefix6 & Hprefix6 & Hnil & Hdone & Hend & Hobs).
    have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
    destruct (segment_101d8_prefix12_covered regs global left right true
      prefix6 done Hx15 Hx12 Hcondition Hprefix6 Hnil HdoneNb) as
      (prefix12 & Hprefix12 & Hsecond).
    destruct (segment_101d8_taken_suffix_covered regs global left right
      prefix12 done labels spawned after Hpc Htaken Hprefix12 Hnil Hdone) as
      (Hafter & Hsuffix).
    split; first exact Hafter.
    rewrite Hsecond in Hobs. repeat rewrite <- app_assoc in Hobs.
    rewrite Hsuffix in Hobs.
    unfold writeSuccess101d8TakenAllObservations.
    rewrite writeSuccess101d8CommonObservationsSplit.
    rewrite app_assoc. exact Hobs.
Qed.

Lemma segment_101d8_covered regs global (left right : bv 64)
    observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  regs !! "x15" = Some (RVal_Bits left) ->
  regs !! "x12" = Some (RVal_Bits right) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101dc = Some a101dc ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e0 = Some a101e0 ->
  writeSuccessTraceAssumptions (writeSuccess101d8Before regs global) ->
  IslaInstructionSegment (writeSuccess101d8Before regs global)
    observations after ->
  after = writeSuccess101d8After left right regs global /\
  observations = writeSuccess101d8Observations left right regs global.
Proof.
  intros Hpc Hx15 Hx12 Hcode Hfall Htaken Hassumptions Hsegment.
  eapply segment_101d8_mstatus_covered; eauto.
  exact (writeSuccess15694MstatusFromTraceAssumptions regs global Hassumptions).
Qed.

Print Assumptions writeSuccess101d8CommonObservationsSplit.
Print Assumptions segment_101d8_mstatus_covered.
Print Assumptions segment_101d8_covered.
