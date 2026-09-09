Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d28.
Require Import IslaTraces.write_success_01.a10190.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28CoverageSuffixFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28CoverageSuffixLast.

Lemma segment_15d28_mstatus_covered regs global observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d28)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess15d28Ra) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d28 = Some a15d28 ->
  global.(seq_instrs) !! Z_to_bv 64 0x10190 = Some a10190 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d28Before regs global)
    observations after ->
  after = writeSuccess15d28After regs global /\
  observations = writeSuccess15d28Observations regs global.
Proof.
  intros Hpc Hx1 Hcode Hnext Hmstatus Hsegment.
  destruct (segment_15d28_prefix8_covered regs global observations after
    Hpc Hx1 Hmstatus Hsegment) as
    (done & labels & spawned & prefix8 & Hprefix8 & Hnil & Hdone & Hend & Hobs).
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (segment_15d28_suffix_first2_covered regs global prefix8 done
    Hprefix8 Hnil HdoneNb) as (prefix10 & Hprefix10 & Hfirst).
  destruct (segment_15d28_suffix_last_covered regs global prefix10 done labels
    spawned after Hpc Hx1 Hnext Hprefix10 Hnil Hdone) as (Hafter & Hlast).
  split; first exact Hafter.
  pose proof (f_equal
    (fun tail => writeSuccess15d28Prefix8Observations regs global ++
      writeSuccess15d28TailFirst2Observations regs global ++ tail)
    Hlast) as Hlift.
  rewrite Hfirst in Hobs. rewrite !app_assoc in Hobs.
  rewrite writeSuccess15d28ObservationsSplit.
  rewrite writeSuccess15d28TailObservationsSplit.
  rewrite !app_assoc.
  etransitivity; first exact Hobs. exact Hlift.
Qed.

Lemma segment_15d28_covered regs global observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d28)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess15d28Ra) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d28 = Some a15d28 ->
  global.(seq_instrs) !! Z_to_bv 64 0x10190 = Some a10190 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d28Before regs global)
    observations after ->
  after = writeSuccess15d28After regs global /\
  observations = writeSuccess15d28Observations regs global.
Proof.
  exact (segment_15d28_mstatus_covered regs global observations after).
Qed.

Print Assumptions segment_15d28_mstatus_covered.
Print Assumptions segment_15d28_covered.
