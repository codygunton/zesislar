Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d1c.
Require Import IslaTraces.write_success_07.a15d20.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d1c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d1cCoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d1cCoverageSuffix.

Lemma writeSuccess15d1cObservationsSplit regs global sp :
  writeSuccess15d1cObservations regs global sp =
  writeSuccess15d1cFirst5Observations regs global sp ++
  writeSuccess15d1cTailObservations regs global sp.
Proof.
  unfold writeSuccess15d1cObservations,
    writeSuccess15d1cFirst5Observations,
    writeSuccess15d1cTailObservations,
    writeSuccess15d1cPrefixObservations. cbn. reflexivity.
Qed.

Lemma segment_15d1c_mstatus_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX10 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d1c)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some oldX10 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d1c = Some a15d1c ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d20 = Some a15d20 ->
  eval_a_exp regs writeSuccess15d1cMstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d1cBefore regs global)
    observations after ->
  after = writeSuccess15d1cAfter regs global sp /\
  observations = writeSuccess15d1cObservations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hmstatus Hsegment.
  destruct (segment_15d1c_prefix5_covered regs global sp observations after
    Hpc Hmstatus Hsegment) as
    (done & labels & spawned & prefix5 & Hprefix5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_15d1c_suffix_covered regs global sp oldX10
    prefix5 done labels spawned after Hpc Hsp Hdest Hnext Hprefix5 Hnil Hdone)
    as (Hafter & Hsuffix).
  split; first exact Hafter.
  repeat rewrite <- app_assoc in Hobs. rewrite Hsuffix in Hobs.
  rewrite writeSuccess15d1cObservationsSplit. exact Hobs.
Qed.

Lemma segment_15d1c_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX10 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d1c)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some oldX10 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d1c = Some a15d1c ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d20 = Some a15d20 ->
  eval_a_exp regs writeSuccess15d1cMstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d1cBefore regs global)
    observations after ->
  after = writeSuccess15d1cAfter regs global sp /\
  observations = writeSuccess15d1cObservations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hmstatus Hsegment.
  eapply segment_15d1c_mstatus_covered; eauto.
Qed.

Print Assumptions writeSuccess15d1cObservationsSplit.
Print Assumptions segment_15d1c_mstatus_covered.
Print Assumptions segment_15d1c_covered.
