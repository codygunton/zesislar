(* Generated from the pinned bnez trace shape. *)
(* The renderer validates the pinned operands and endpoints. *)
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_95.a156e4.
Require Import IslaTraces.write_success_96.a156e8.
Require Import IslaTraces.write_success_90.a15694.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e4CoveragePrefix6.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e4CoveragePrefix10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e4CoverageTaken.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e4CoverageFallthrough.

Lemma writeSuccess156e4CommonObservationsSplit value condition regs global :
  writeSuccess156e4CommonObservations value condition regs global =
  writeSuccess156e4First6Observations value condition regs global ++
  writeSuccess156e4Second4Observations value condition regs global.
Proof.
  unfold writeSuccess156e4First6Observations,
    writeSuccess156e4Second4Observations,
    writeSuccess156e4CommonObservations, writeSuccess156e4CommonLocals.
  cbn. reflexivity.
Qed.

Lemma segment_156e4_mstatus_covered regs global (value : bv 64)
    observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156e4)) ->
  regs !! "x9" = Some (RVal_Bits value) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e4 = Some a156e4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e8 = Some a156e8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15694 = Some a15694 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156e4Before regs global)
    observations after ->
  after = writeSuccess156e4After value regs global /\
  observations = writeSuccess156e4Observations value regs global.
Proof.
  intros Hpc Hx9 Hcode Hfall Htaken Hmstatus Hsegment.
  unfold writeSuccess156e4After, writeSuccess156e4Observations.
  destruct (decide (value = (BV 64 0))) as [Heq|Hne].
  - have Hcondition := writeSuccess156e4ConditionFallthrough value Heq.
    destruct (segment_156e4_prefix6_covered regs global value false
      observations after Hpc Hmstatus Hsegment) as
      (done & labels & spawned & prefix6 & Hprefix6 & Hnil & Hdone & Hend & Hobs).
    have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
    destruct (segment_156e4_prefix10_covered regs global value false
      prefix6 done Hx9 Hcondition Hprefix6 Hnil HdoneNb) as
      (prefix10 & Hprefix10 & Hsecond).
    destruct (segment_156e4_fallthrough_suffix_covered regs global value
      prefix10 done labels spawned after Hpc Hfall Hprefix10 Hnil Hdone) as
      (Hafter & Hsuffix).
    split; first exact Hafter.
    rewrite Hsecond in Hobs. repeat rewrite <- app_assoc in Hobs.
    rewrite Hsuffix in Hobs.
    unfold writeSuccess156e4FallthroughAllObservations.
    rewrite writeSuccess156e4CommonObservationsSplit.
    rewrite app_assoc. exact Hobs.
  - have Hcondition := writeSuccess156e4ConditionTaken value Hne.
    destruct (segment_156e4_prefix6_covered regs global value true
      observations after Hpc Hmstatus Hsegment) as
      (done & labels & spawned & prefix6 & Hprefix6 & Hnil & Hdone & Hend & Hobs).
    have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
    destruct (segment_156e4_prefix10_covered regs global value true
      prefix6 done Hx9 Hcondition Hprefix6 Hnil HdoneNb) as
      (prefix10 & Hprefix10 & Hsecond).
    destruct (segment_156e4_taken_suffix_covered regs global value
      prefix10 done labels spawned after Hpc Htaken Hprefix10 Hnil Hdone) as
      (Hafter & Hsuffix).
    split; first exact Hafter.
    rewrite Hsecond in Hobs. repeat rewrite <- app_assoc in Hobs.
    rewrite Hsuffix in Hobs.
    unfold writeSuccess156e4TakenAllObservations.
    rewrite writeSuccess156e4CommonObservationsSplit.
    rewrite app_assoc. exact Hobs.
Qed.

Lemma segment_156e4_covered regs global (value : bv 64)
    observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156e4)) ->
  regs !! "x9" = Some (RVal_Bits value) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e4 = Some a156e4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e8 = Some a156e8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15694 = Some a15694 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156e4Before regs global)
    observations after ->
  after = writeSuccess156e4After value regs global /\
  observations = writeSuccess156e4Observations value regs global.
Proof.
  intros Hpc Hx9 Hcode Hfall Htaken Hmstatus Hsegment.
  eapply segment_156e4_mstatus_covered; eauto.
Qed.

Print Assumptions writeSuccess156e4CommonObservationsSplit.
Print Assumptions segment_156e4_mstatus_covered.
Print Assumptions segment_156e4_covered.
