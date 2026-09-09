Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_90.a15694.
Require Import IslaTraces.write_success_90.a15698.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694CoverageSuffix.

Lemma writeSuccess15694ObservationsSplit regs global sp :
  writeSuccess15694Observations regs global sp =
  writeSuccess15694First5Observations regs global sp ++
  writeSuccess15694TailObservations regs global sp.
Proof.
  unfold writeSuccess15694Observations,
    writeSuccess15694First5Observations,
    writeSuccess15694TailObservations,
    writeSuccess15694PrefixObservations. cbn. reflexivity.
Qed.

Lemma segment_15694_mstatus_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX10 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15694)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some oldX10 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15694 = Some a15694 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15698 = Some a15698 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15694Before regs global)
    observations after ->
  after = writeSuccess15694After regs global sp /\
  observations = writeSuccess15694Observations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hmstatus Hsegment.
  destruct (segment_15694_prefix5_covered regs global sp observations after
    Hpc Hmstatus Hsegment) as
    (done & labels & spawned & prefix5 & Hprefix5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_15694_suffix_covered regs global sp oldX10
    prefix5 done labels spawned after Hpc Hsp Hdest Hnext Hprefix5 Hnil Hdone)
    as (Hafter & Hsuffix).
  split; first exact Hafter.
  repeat rewrite <- app_assoc in Hobs. rewrite Hsuffix in Hobs.
  rewrite writeSuccess15694ObservationsSplit. exact Hobs.
Qed.

Lemma segment_15694_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX10 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15694)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some oldX10 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15694 = Some a15694 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15698 = Some a15698 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15694Before regs global)
    observations after ->
  after = writeSuccess15694After regs global sp /\
  observations = writeSuccess15694Observations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hmstatus Hsegment.
  eapply segment_15694_mstatus_covered; eauto.
Qed.

Print Assumptions writeSuccess15694ObservationsSplit.
Print Assumptions segment_15694_mstatus_covered.
Print Assumptions segment_15694_covered.
