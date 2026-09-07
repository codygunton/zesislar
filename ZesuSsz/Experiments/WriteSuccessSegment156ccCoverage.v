Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_93.a156cc.
Require Import IslaTraces.write_success_01.a10190.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156cc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156ccCoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156ccCoverageSuffixFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156ccCoverageSuffixLast.

Lemma segment_156cc_mstatus_covered regs global observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156cc)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156ccRa) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156cc = Some a156cc ->
  global.(seq_instrs) !! Z_to_bv 64 0x10190 = Some a10190 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156ccBefore regs global)
    observations after ->
  after = writeSuccess156ccAfter regs global /\
  observations = writeSuccess156ccObservations regs global.
Proof.
  intros Hpc Hx1 Hcode Hnext Hmstatus Hsegment.
  destruct (segment_156cc_prefix8_covered regs global observations after
    Hpc Hx1 Hmstatus Hsegment) as
    (done & labels & spawned & prefix8 & Hprefix8 & Hnil & Hdone & Hend & Hobs).
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (segment_156cc_suffix_first2_covered regs global prefix8 done
    Hprefix8 Hnil HdoneNb) as (prefix10 & Hprefix10 & Hfirst).
  destruct (segment_156cc_suffix_last_covered regs global prefix10 done labels
    spawned after Hpc Hx1 Hnext Hprefix10 Hnil Hdone) as (Hafter & Hlast).
  split; first exact Hafter.
  pose proof (f_equal
    (fun tail => writeSuccess156ccPrefix8Observations regs global ++
      writeSuccess156ccTailFirst2Observations regs global ++ tail)
    Hlast) as Hlift.
  rewrite Hfirst in Hobs. rewrite !app_assoc in Hobs.
  rewrite writeSuccess156ccObservationsSplit.
  rewrite writeSuccess156ccTailObservationsSplit.
  rewrite !app_assoc.
  etransitivity; first exact Hobs. exact Hlift.
Qed.

Lemma segment_156cc_covered regs global observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156cc)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156ccRa) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156cc = Some a156cc ->
  global.(seq_instrs) !! Z_to_bv 64 0x10190 = Some a10190 ->
  writeSuccessTraceAssumptions (writeSuccess156ccBefore regs global) ->
  IslaInstructionSegment (writeSuccess156ccBefore regs global)
    observations after ->
  after = writeSuccess156ccAfter regs global /\
  observations = writeSuccess156ccObservations regs global.
Proof.
  intros Hpc Hx1 Hcode Hnext Hassumptions Hsegment.
  eapply segment_156cc_mstatus_covered; eauto.
  exact (writeSuccess15694MstatusFromTraceAssumptions regs global Hassumptions).
Qed.

Print Assumptions segment_156cc_mstatus_covered.
Print Assumptions segment_156cc_covered.
