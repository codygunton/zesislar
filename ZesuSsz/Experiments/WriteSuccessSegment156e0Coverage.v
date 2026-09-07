Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_95.a156e0.
Require Import IslaTraces.write_success_95.a156e4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e0CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e0CoverageSuffix.

Lemma writeSuccess156e0ObservationsSplit regs global sp :
  writeSuccess156e0Observations regs global sp =
  writeSuccess156e0First5Observations regs global sp ++
  writeSuccess156e0TailObservations regs global sp.
Proof.
  unfold writeSuccess156e0Observations,
    writeSuccess156e0First5Observations,
    writeSuccess156e0TailObservations,
    writeSuccess156e0PrefixObservations. cbn. reflexivity.
Qed.

Lemma segment_156e0_mstatus_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX9 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156e0)) ->
  regs !! "x9" = Some (RVal_Bits sp) ->
  regs !! "x9" = Some oldX9 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e0 = Some a156e0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e4 = Some a156e4 ->
  eval_a_exp regs writeSuccess156e0Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156e0Before regs global)
    observations after ->
  after = writeSuccess156e0After regs global sp /\
  observations = writeSuccess156e0Observations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hmstatus Hsegment.
  destruct (segment_156e0_prefix5_covered regs global sp observations after
    Hpc Hmstatus Hsegment) as
    (done & labels & spawned & prefix5 & Hprefix5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_156e0_suffix_covered regs global sp oldX9
    prefix5 done labels spawned after Hpc Hsp Hdest Hnext Hprefix5 Hnil Hdone)
    as (Hafter & Hsuffix).
  split; first exact Hafter.
  repeat rewrite <- app_assoc in Hobs. rewrite Hsuffix in Hobs.
  rewrite writeSuccess156e0ObservationsSplit. exact Hobs.
Qed.

Lemma segment_156e0_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX9 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156e0)) ->
  regs !! "x9" = Some (RVal_Bits sp) ->
  regs !! "x9" = Some oldX9 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e0 = Some a156e0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e4 = Some a156e4 ->
  writeSuccessTraceAssumptions (writeSuccess156e0Before regs global) ->
  IslaInstructionSegment (writeSuccess156e0Before regs global)
    observations after ->
  after = writeSuccess156e0After regs global sp /\
  observations = writeSuccess156e0Observations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hassumptions Hsegment.
  eapply segment_156e0_mstatus_covered; eauto.
  exact (writeSuccess156e0MstatusFromTraceAssumptions regs global Hassumptions).
Qed.

Print Assumptions writeSuccess156e0ObservationsSplit.
Print Assumptions segment_156e0_mstatus_covered.
Print Assumptions segment_156e0_covered.
