Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_90.a1569c.
Require Import IslaTraces.write_success_90.a156a0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1569c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1569cCoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1569cCoverageSuffix.

Lemma writeSuccess1569cObservationsSplit regs global sp :
  writeSuccess1569cObservations regs global sp =
  writeSuccess1569cFirst5Observations regs global sp ++
  writeSuccess1569cTailObservations regs global sp.
Proof.
  unfold writeSuccess1569cObservations,
    writeSuccess1569cFirst5Observations,
    writeSuccess1569cTailObservations,
    writeSuccess1569cPrefixObservations. cbn. reflexivity.
Qed.

Lemma segment_1569c_mstatus_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX11 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x1569c)) ->
  regs !! "x8" = Some (RVal_Bits sp) ->
  regs !! "x11" = Some oldX11 ->
  global.(seq_instrs) !! Z_to_bv 64 0x1569c = Some a1569c ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a0 = Some a156a0 ->
  eval_a_exp regs writeSuccess1569cMstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess1569cBefore regs global)
    observations after ->
  after = writeSuccess1569cAfter regs global sp /\
  observations = writeSuccess1569cObservations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hmstatus Hsegment.
  destruct (segment_1569c_prefix5_covered regs global sp observations after
    Hpc Hmstatus Hsegment) as
    (done & labels & spawned & prefix5 & Hprefix5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_1569c_suffix_covered regs global sp oldX11
    prefix5 done labels spawned after Hpc Hsp Hdest Hnext Hprefix5 Hnil Hdone)
    as (Hafter & Hsuffix).
  split; first exact Hafter.
  repeat rewrite <- app_assoc in Hobs. rewrite Hsuffix in Hobs.
  rewrite writeSuccess1569cObservationsSplit. exact Hobs.
Qed.

Lemma segment_1569c_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX11 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x1569c)) ->
  regs !! "x8" = Some (RVal_Bits sp) ->
  regs !! "x11" = Some oldX11 ->
  global.(seq_instrs) !! Z_to_bv 64 0x1569c = Some a1569c ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a0 = Some a156a0 ->
  eval_a_exp regs writeSuccess1569cMstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess1569cBefore regs global)
    observations after ->
  after = writeSuccess1569cAfter regs global sp /\
  observations = writeSuccess1569cObservations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hmstatus Hsegment.
  eapply segment_1569c_mstatus_covered; eauto.
Qed.

Print Assumptions writeSuccess1569cObservationsSplit.
Print Assumptions segment_1569c_mstatus_covered.
Print Assumptions segment_1569c_covered.
