Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_01.a10194.
Require Import IslaTraces.write_success_01.a10198.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10194.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10194CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10194CoverageSuffix.

Lemma writeSuccess10194ObservationsSplit regs global sp :
  writeSuccess10194Observations regs global sp =
  writeSuccess10194First5Observations regs global sp ++
  writeSuccess10194TailObservations regs global sp.
Proof.
  unfold writeSuccess10194Observations,
    writeSuccess10194First5Observations,
    writeSuccess10194TailObservations,
    writeSuccess10194PrefixObservations. cbn. reflexivity.
Qed.

Lemma segment_10194_mstatus_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX5 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10194)) ->
  regs !! "x5" = Some (RVal_Bits sp) ->
  regs !! "x5" = Some oldX5 ->
  global.(seq_instrs) !! Z_to_bv 64 0x10194 = Some a10194 ->
  global.(seq_instrs) !! Z_to_bv 64 0x10198 = Some a10198 ->
  eval_a_exp regs writeSuccess10194Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess10194Before regs global)
    observations after ->
  after = writeSuccess10194After regs global sp /\
  observations = writeSuccess10194Observations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hmstatus Hsegment.
  destruct (segment_10194_prefix5_covered regs global sp observations after
    Hpc Hmstatus Hsegment) as
    (done & labels & spawned & prefix5 & Hprefix5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_10194_suffix_covered regs global sp oldX5
    prefix5 done labels spawned after Hpc Hsp Hdest Hnext Hprefix5 Hnil Hdone)
    as (Hafter & Hsuffix).
  split; first exact Hafter.
  repeat rewrite <- app_assoc in Hobs. rewrite Hsuffix in Hobs.
  rewrite writeSuccess10194ObservationsSplit. exact Hobs.
Qed.

Lemma segment_10194_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX5 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10194)) ->
  regs !! "x5" = Some (RVal_Bits sp) ->
  regs !! "x5" = Some oldX5 ->
  global.(seq_instrs) !! Z_to_bv 64 0x10194 = Some a10194 ->
  global.(seq_instrs) !! Z_to_bv 64 0x10198 = Some a10198 ->
  writeSuccessTraceAssumptions (writeSuccess10194Before regs global) ->
  IslaInstructionSegment (writeSuccess10194Before regs global)
    observations after ->
  after = writeSuccess10194After regs global sp /\
  observations = writeSuccess10194Observations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hassumptions Hsegment.
  eapply segment_10194_mstatus_covered; eauto.
  exact (writeSuccess10194MstatusFromTraceAssumptions regs global Hassumptions).
Qed.

Print Assumptions writeSuccess10194ObservationsSplit.
Print Assumptions segment_10194_mstatus_covered.
Print Assumptions segment_10194_covered.
