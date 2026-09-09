Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d10.
Require Import IslaTraces.write_success_07.a15d14.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10CoverageSuffix.

Lemma writeSuccess15d10ObservationsSplit regs global sp :
  writeSuccess15d10Observations regs global sp =
  writeSuccess15d10First5Observations regs global sp ++
  writeSuccess15d10TailObservations regs global sp.
Proof.
  unfold writeSuccess15d10Observations,
    writeSuccess15d10First5Observations,
    writeSuccess15d10TailObservations,
    writeSuccess15d10PrefixObservations. cbn. reflexivity.
Qed.

Lemma segment_15d10_mstatus_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX2 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d10)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x2" = Some oldX2 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d10 = Some a15d10 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d14 = Some a15d14 ->
  eval_a_exp regs writeSuccess15d10Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d10Before regs global)
    observations after ->
  after = writeSuccess15d10After regs global sp /\
  observations = writeSuccess15d10Observations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hmstatus Hsegment.
  destruct (segment_15d10_prefix5_covered regs global sp observations after
    Hpc Hmstatus Hsegment) as
    (done & labels & spawned & prefix5 & Hprefix5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_15d10_suffix_covered regs global sp oldX2
    prefix5 done labels spawned after Hpc Hsp Hdest Hnext Hprefix5 Hnil Hdone)
    as (Hafter & Hsuffix).
  split; first exact Hafter.
  repeat rewrite <- app_assoc in Hobs. rewrite Hsuffix in Hobs.
  rewrite writeSuccess15d10ObservationsSplit. exact Hobs.
Qed.

Lemma segment_15d10_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX2 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d10)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x2" = Some oldX2 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d10 = Some a15d10 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d14 = Some a15d14 ->
  eval_a_exp regs writeSuccess15d10Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d10Before regs global)
    observations after ->
  after = writeSuccess15d10After regs global sp /\
  observations = writeSuccess15d10Observations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hmstatus Hsegment.
  eapply segment_15d10_mstatus_covered; eauto.
Qed.

Print Assumptions writeSuccess15d10ObservationsSplit.
Print Assumptions segment_15d10_mstatus_covered.
Print Assumptions segment_15d10_covered.
