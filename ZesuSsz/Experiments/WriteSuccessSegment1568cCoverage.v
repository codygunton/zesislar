Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_89.a1568c.
Require Import IslaTraces.write_success_89.a15690.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1568c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1568cCoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1568cCoverageSuffix.

Lemma writeSuccess1568cObservationsSplit regs global sp :
  writeSuccess1568cObservations regs global sp =
  writeSuccess1568cFirst5Observations regs global sp ++
  writeSuccess1568cTailObservations regs global sp.
Proof.
  unfold writeSuccess1568cObservations,
    writeSuccess1568cFirst5Observations,
    writeSuccess1568cTailObservations,
    writeSuccess1568cPrefixObservations. cbn. reflexivity.
Qed.

Lemma segment_1568c_mstatus_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX18 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x1568c)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x18" = Some oldX18 ->
  global.(seq_instrs) !! Z_to_bv 64 0x1568c = Some a1568c ->
  global.(seq_instrs) !! Z_to_bv 64 0x15690 = Some a15690 ->
  eval_a_exp regs writeSuccess1568cMstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess1568cBefore regs global)
    observations after ->
  after = writeSuccess1568cAfter regs global sp /\
  observations = writeSuccess1568cObservations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hmstatus Hsegment.
  destruct (segment_1568c_prefix5_covered regs global sp observations after
    Hpc Hmstatus Hsegment) as
    (done & labels & spawned & prefix5 & Hprefix5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_1568c_suffix_covered regs global sp oldX18
    prefix5 done labels spawned after Hpc Hsp Hdest Hnext Hprefix5 Hnil Hdone)
    as (Hafter & Hsuffix).
  split; first exact Hafter.
  repeat rewrite <- app_assoc in Hobs. rewrite Hsuffix in Hobs.
  rewrite writeSuccess1568cObservationsSplit. exact Hobs.
Qed.

Lemma segment_1568c_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX18 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x1568c)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x18" = Some oldX18 ->
  global.(seq_instrs) !! Z_to_bv 64 0x1568c = Some a1568c ->
  global.(seq_instrs) !! Z_to_bv 64 0x15690 = Some a15690 ->
  eval_a_exp regs writeSuccess1568cMstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess1568cBefore regs global)
    observations after ->
  after = writeSuccess1568cAfter regs global sp /\
  observations = writeSuccess1568cObservations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hmstatus Hsegment.
  eapply segment_1568c_mstatus_covered; eauto.
Qed.

Print Assumptions writeSuccess1568cObservationsSplit.
Print Assumptions segment_1568c_mstatus_covered.
Print Assumptions segment_1568c_covered.
