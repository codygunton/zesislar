Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d30.
Require Import IslaTraces.write_success_07.a15d34.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d30.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d30CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d30CoverageSuffix.

Lemma writeSuccess15d30ObservationsSplit regs global sp :
  writeSuccess15d30Observations regs global sp =
  writeSuccess15d30First5Observations regs global sp ++
  writeSuccess15d30TailObservations regs global sp.
Proof.
  unfold writeSuccess15d30Observations,
    writeSuccess15d30First5Observations,
    writeSuccess15d30TailObservations,
    writeSuccess15d30PrefixObservations. cbn. reflexivity.
Qed.

Lemma segment_15d30_mstatus_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX2 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d30)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x2" = Some oldX2 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d30 = Some a15d30 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d34 = Some a15d34 ->
  eval_a_exp regs writeSuccess15d30Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d30Before regs global)
    observations after ->
  after = writeSuccess15d30After regs global sp /\
  observations = writeSuccess15d30Observations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hmstatus Hsegment.
  destruct (segment_15d30_prefix5_covered regs global sp observations after
    Hpc Hmstatus Hsegment) as
    (done & labels & spawned & prefix5 & Hprefix5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_15d30_suffix_covered regs global sp oldX2
    prefix5 done labels spawned after Hpc Hsp Hdest Hnext Hprefix5 Hnil Hdone)
    as (Hafter & Hsuffix).
  split; first exact Hafter.
  repeat rewrite <- app_assoc in Hobs. rewrite Hsuffix in Hobs.
  rewrite writeSuccess15d30ObservationsSplit. exact Hobs.
Qed.

Lemma segment_15d30_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX2 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d30)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x2" = Some oldX2 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d30 = Some a15d30 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d34 = Some a15d34 ->
  writeSuccessTraceAssumptions (writeSuccess15d30Before regs global) ->
  IslaInstructionSegment (writeSuccess15d30Before regs global)
    observations after ->
  after = writeSuccess15d30After regs global sp /\
  observations = writeSuccess15d30Observations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hassumptions Hsegment.
  eapply segment_15d30_mstatus_covered; eauto.
  exact (writeSuccess15d30MstatusFromTraceAssumptions regs global Hassumptions).
Qed.

Print Assumptions writeSuccess15d30ObservationsSplit.
Print Assumptions segment_15d30_mstatus_covered.
Print Assumptions segment_15d30_covered.
