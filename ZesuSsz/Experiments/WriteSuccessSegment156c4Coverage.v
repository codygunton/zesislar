Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_93.a156c4.
Require Import IslaTraces.write_success_93.a156c8.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c4CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c4CoverageSuffix.

Lemma writeSuccess156c4ObservationsSplit regs global sp :
  writeSuccess156c4Observations regs global sp =
  writeSuccess156c4First5Observations regs global sp ++
  writeSuccess156c4TailObservations regs global sp.
Proof.
  unfold writeSuccess156c4Observations,
    writeSuccess156c4First5Observations,
    writeSuccess156c4TailObservations,
    writeSuccess156c4PrefixObservations. cbn. reflexivity.
Qed.

Lemma segment_156c4_mstatus_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX10 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c4)) ->
  regs !! "x18" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some oldX10 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156c4 = Some a156c4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156c8 = Some a156c8 ->
  eval_a_exp regs writeSuccess156c4Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156c4Before regs global)
    observations after ->
  after = writeSuccess156c4After regs global sp /\
  observations = writeSuccess156c4Observations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hmstatus Hsegment.
  destruct (segment_156c4_prefix5_covered regs global sp observations after
    Hpc Hmstatus Hsegment) as
    (done & labels & spawned & prefix5 & Hprefix5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_156c4_suffix_covered regs global sp oldX10
    prefix5 done labels spawned after Hpc Hsp Hdest Hnext Hprefix5 Hnil Hdone)
    as (Hafter & Hsuffix).
  split; first exact Hafter.
  repeat rewrite <- app_assoc in Hobs. rewrite Hsuffix in Hobs.
  rewrite writeSuccess156c4ObservationsSplit. exact Hobs.
Qed.

Lemma segment_156c4_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX10 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c4)) ->
  regs !! "x18" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some oldX10 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156c4 = Some a156c4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156c8 = Some a156c8 ->
  writeSuccessTraceAssumptions (writeSuccess156c4Before regs global) ->
  IslaInstructionSegment (writeSuccess156c4Before regs global)
    observations after ->
  after = writeSuccess156c4After regs global sp /\
  observations = writeSuccess156c4Observations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hassumptions Hsegment.
  eapply segment_156c4_mstatus_covered; eauto.
  exact (writeSuccess156c4MstatusFromTraceAssumptions regs global Hassumptions).
Qed.

Print Assumptions writeSuccess156c4ObservationsSplit.
Print Assumptions segment_156c4_mstatus_covered.
Print Assumptions segment_156c4_covered.
