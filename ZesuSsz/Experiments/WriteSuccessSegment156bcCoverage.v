Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_92.a156bc.
Require Import IslaTraces.write_success_07.a15d10.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156bc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156bcCoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156bcCoverageSuffixFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156bcCoverageSuffixLast.

Lemma segment_156bc_mstatus_covered regs global observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156bc)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156bcRa) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156bc = Some a156bc ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d10 = Some a15d10 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156bcBefore regs global)
    observations after ->
  after = writeSuccess156bcAfter regs global /\
  observations = writeSuccess156bcObservations regs global.
Proof.
  intros Hpc Hx1 Hcode Hnext Hmstatus Hsegment.
  destruct (segment_156bc_prefix8_covered regs global observations after
    Hpc Hx1 Hmstatus Hsegment) as
    (done & labels & spawned & prefix8 & Hprefix8 & Hnil & Hdone & Hend & Hobs).
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (segment_156bc_suffix_first2_covered regs global prefix8 done
    Hprefix8 Hnil HdoneNb) as (prefix10 & Hprefix10 & Hfirst).
  destruct (segment_156bc_suffix_last_covered regs global prefix10 done labels
    spawned after Hpc Hx1 Hnext Hprefix10 Hnil Hdone) as (Hafter & Hlast).
  split; first exact Hafter.
  pose proof (f_equal
    (fun tail => writeSuccess156bcPrefix8Observations regs global ++
      writeSuccess156bcTailFirst2Observations regs global ++ tail)
    Hlast) as Hlift.
  rewrite Hfirst in Hobs. rewrite !app_assoc in Hobs.
  rewrite writeSuccess156bcObservationsSplit.
  rewrite writeSuccess156bcTailObservationsSplit.
  rewrite !app_assoc.
  etransitivity; first exact Hobs. exact Hlift.
Qed.

Lemma segment_156bc_covered regs global observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156bc)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156bcRa) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156bc = Some a156bc ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d10 = Some a15d10 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156bcBefore regs global)
    observations after ->
  after = writeSuccess156bcAfter regs global /\
  observations = writeSuccess156bcObservations regs global.
Proof.
  exact (segment_156bc_mstatus_covered regs global observations after).
Qed.

Print Assumptions segment_156bc_mstatus_covered.
Print Assumptions segment_156bc_covered.
