Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_95.a156dc.
Require Import IslaTraces.write_success_95.a156e0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156dc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156dcCoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156dcCoverageSuffix.

Lemma writeSuccess156dcObservationsSplit regs global sp :
  writeSuccess156dcObservations regs global sp =
  writeSuccess156dcFirst5Observations regs global sp ++
  writeSuccess156dcTailObservations regs global sp.
Proof.
  unfold writeSuccess156dcObservations,
    writeSuccess156dcFirst5Observations,
    writeSuccess156dcTailObservations,
    writeSuccess156dcPrefixObservations. cbn. reflexivity.
Qed.

Lemma segment_156dc_mstatus_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX8 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156dc)) ->
  regs !! "x8" = Some (RVal_Bits sp) ->
  regs !! "x8" = Some oldX8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156dc = Some a156dc ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e0 = Some a156e0 ->
  eval_a_exp regs writeSuccess156dcMstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156dcBefore regs global)
    observations after ->
  after = writeSuccess156dcAfter regs global sp /\
  observations = writeSuccess156dcObservations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hmstatus Hsegment.
  destruct (segment_156dc_prefix5_covered regs global sp observations after
    Hpc Hmstatus Hsegment) as
    (done & labels & spawned & prefix5 & Hprefix5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_156dc_suffix_covered regs global sp oldX8
    prefix5 done labels spawned after Hpc Hsp Hdest Hnext Hprefix5 Hnil Hdone)
    as (Hafter & Hsuffix).
  split; first exact Hafter.
  repeat rewrite <- app_assoc in Hobs. rewrite Hsuffix in Hobs.
  rewrite writeSuccess156dcObservationsSplit. exact Hobs.
Qed.

Lemma segment_156dc_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX8 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156dc)) ->
  regs !! "x8" = Some (RVal_Bits sp) ->
  regs !! "x8" = Some oldX8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156dc = Some a156dc ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e0 = Some a156e0 ->
  eval_a_exp regs writeSuccess156dcMstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156dcBefore regs global)
    observations after ->
  after = writeSuccess156dcAfter regs global sp /\
  observations = writeSuccess156dcObservations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hmstatus Hsegment.
  eapply segment_156dc_mstatus_covered; eauto.
Qed.

Print Assumptions writeSuccess156dcObservationsSplit.
Print Assumptions segment_156dc_mstatus_covered.
Print Assumptions segment_156dc_covered.
