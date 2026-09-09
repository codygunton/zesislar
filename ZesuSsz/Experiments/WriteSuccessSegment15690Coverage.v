(* Instantiated from the pinned 0x15690 beqz trace shape. *)
(* The renderer validates the pinned operands and endpoints. *)
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_89.a15690.
Require Import IslaTraces.write_success_90.a15694.
Require Import IslaTraces.write_success_96.a156e8.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15690.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15690CoveragePrefix6.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15690CoveragePrefix10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15690CoverageTaken.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15690CoverageFallthrough.

Lemma writeSuccess15690CommonObservationsSplit value condition regs global :
  writeSuccess15690CommonObservations value condition regs global =
  writeSuccess15690First6Observations value condition regs global ++
  writeSuccess15690Second4Observations value condition regs global.
Proof.
  unfold writeSuccess15690First6Observations,
    writeSuccess15690Second4Observations,
    writeSuccess15690CommonObservations, writeSuccess15690CommonLocals.
  cbn. reflexivity.
Qed.

Lemma segment_15690_mstatus_covered regs global (value : bv 64)
    observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15690)) ->
  regs !! "x9" = Some (RVal_Bits value) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15690 = Some a15690 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15694 = Some a15694 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e8 = Some a156e8 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15690Before regs global)
    observations after ->
  after = writeSuccess15690After value regs global /\
  observations = writeSuccess15690Observations value regs global.
Proof.
  intros Hpc Hx9 Hcode Hfall Htaken Hmstatus Hsegment.
  unfold writeSuccess15690After, writeSuccess15690Observations.
  destruct (decide (value = (BV 64 0))) as [Heq|Hne].
  - have Hcondition := writeSuccess15690ConditionTaken value Heq.
    destruct (segment_15690_prefix6_covered regs global value true
      observations after Hpc Hmstatus Hsegment) as
      (done & labels & spawned & prefix6 & Hprefix6 & Hnil & Hdone & Hend & Hobs).
    have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
    destruct (segment_15690_prefix10_covered regs global value true
      prefix6 done Hx9 Hcondition Hprefix6 Hnil HdoneNb) as
      (prefix10 & Hprefix10 & Hsecond).
    destruct (segment_15690_taken_suffix_covered regs global value
      prefix10 done labels spawned after Hpc Htaken Hprefix10 Hnil Hdone) as
      (Hafter & Hsuffix).
    split; first exact Hafter.
    rewrite Hsecond in Hobs. repeat rewrite <- app_assoc in Hobs.
    rewrite Hsuffix in Hobs.
    unfold writeSuccess15690TakenAllObservations.
    rewrite writeSuccess15690CommonObservationsSplit.
    rewrite app_assoc. exact Hobs.
  - have Hcondition := writeSuccess15690ConditionFallthrough value Hne.
    destruct (segment_15690_prefix6_covered regs global value false
      observations after Hpc Hmstatus Hsegment) as
      (done & labels & spawned & prefix6 & Hprefix6 & Hnil & Hdone & Hend & Hobs).
    have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
    destruct (segment_15690_prefix10_covered regs global value false
      prefix6 done Hx9 Hcondition Hprefix6 Hnil HdoneNb) as
      (prefix10 & Hprefix10 & Hsecond).
    destruct (segment_15690_fallthrough_suffix_covered regs global value
      prefix10 done labels spawned after Hpc Hfall Hprefix10 Hnil Hdone) as
      (Hafter & Hsuffix).
    split; first exact Hafter.
    rewrite Hsecond in Hobs. repeat rewrite <- app_assoc in Hobs.
    rewrite Hsuffix in Hobs.
    unfold writeSuccess15690FallthroughAllObservations.
    rewrite writeSuccess15690CommonObservationsSplit.
    rewrite app_assoc. exact Hobs.
Qed.

Lemma segment_15690_covered regs global (value : bv 64)
    observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15690)) ->
  regs !! "x9" = Some (RVal_Bits value) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15690 = Some a15690 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15694 = Some a15694 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e8 = Some a156e8 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15690Before regs global)
    observations after ->
  after = writeSuccess15690After value regs global /\
  observations = writeSuccess15690Observations value regs global.
Proof.
  intros Hpc Hx9 Hcode Hfall Htaken Hmstatus Hsegment.
  eapply segment_15690_mstatus_covered; eauto.
Qed.

Print Assumptions writeSuccess15690CommonObservationsSplit.
Print Assumptions segment_15690_mstatus_covered.
Print Assumptions segment_15690_covered.
