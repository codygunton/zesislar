Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_91.a156b0.
Require Import IslaTraces.write_success_07.a15d10.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b0CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b0CoverageSuffixFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b0CoverageSuffixLast.

Lemma segment_156b0_mstatus_covered regs global observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b0)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156b0Ra) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b0 = Some a156b0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d10 = Some a15d10 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156b0Before regs global)
    observations after ->
  after = writeSuccess156b0After regs global /\
  observations = writeSuccess156b0Observations regs global.
Proof.
  intros Hpc Hx1 Hcode Hnext Hmstatus Hsegment.
  destruct (segment_156b0_prefix8_covered regs global observations after
    Hpc Hx1 Hmstatus Hsegment) as
    (done & labels & spawned & prefix8 & Hprefix8 & Hnil & Hdone & Hend & Hobs).
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (segment_156b0_suffix_first2_covered regs global prefix8 done
    Hprefix8 Hnil HdoneNb) as (prefix10 & Hprefix10 & Hfirst).
  destruct (segment_156b0_suffix_last_covered regs global prefix10 done labels
    spawned after Hpc Hx1 Hnext Hprefix10 Hnil Hdone) as (Hafter & Hlast).
  split; first exact Hafter.
  pose proof (f_equal
    (fun tail => writeSuccess156b0Prefix8Observations regs global ++
      writeSuccess156b0TailFirst2Observations regs global ++ tail)
    Hlast) as Hlift.
  rewrite Hfirst in Hobs. rewrite !app_assoc in Hobs.
  rewrite writeSuccess156b0ObservationsSplit.
  rewrite writeSuccess156b0TailObservationsSplit.
  rewrite !app_assoc.
  etransitivity; first exact Hobs. exact Hlift.
Qed.

Lemma segment_156b0_covered regs global observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b0)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156b0Ra) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b0 = Some a156b0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d10 = Some a15d10 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156b0Before regs global)
    observations after ->
  after = writeSuccess156b0After regs global /\
  observations = writeSuccess156b0Observations regs global.
Proof.
  exact (segment_156b0_mstatus_covered regs global observations after).
Qed.

Print Assumptions segment_156b0_mstatus_covered.
Print Assumptions segment_156b0_covered.
