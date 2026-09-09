Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_90.a156a4.
Require Import IslaTraces.write_success_02.a101d4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a4CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a4CoverageSuffixFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a4CoverageSuffixLast.

Lemma segment_156a4_mstatus_covered regs global observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a4)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156a4Ra) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a4 = Some a156a4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d4 = Some a101d4 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156a4Before regs global)
    observations after ->
  after = writeSuccess156a4After regs global /\
  observations = writeSuccess156a4Observations regs global.
Proof.
  intros Hpc Hx1 Hcode Hnext Hmstatus Hsegment.
  destruct (segment_156a4_prefix8_covered regs global observations after
    Hpc Hx1 Hmstatus Hsegment) as
    (done & labels & spawned & prefix8 & Hprefix8 & Hnil & Hdone & Hend & Hobs).
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (segment_156a4_suffix_first2_covered regs global prefix8 done
    Hprefix8 Hnil HdoneNb) as (prefix10 & Hprefix10 & Hfirst).
  destruct (segment_156a4_suffix_last_covered regs global prefix10 done labels
    spawned after Hpc Hx1 Hnext Hprefix10 Hnil Hdone) as (Hafter & Hlast).
  split; first exact Hafter.
  pose proof (f_equal
    (fun tail => writeSuccess156a4Prefix8Observations regs global ++
      writeSuccess156a4TailFirst2Observations regs global ++ tail)
    Hlast) as Hlift.
  rewrite Hfirst in Hobs. rewrite !app_assoc in Hobs.
  rewrite writeSuccess156a4ObservationsSplit.
  rewrite writeSuccess156a4TailObservationsSplit.
  rewrite !app_assoc.
  etransitivity; first exact Hobs. exact Hlift.
Qed.

Lemma segment_156a4_covered regs global observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a4)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156a4Ra) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a4 = Some a156a4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d4 = Some a101d4 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156a4Before regs global)
    observations after ->
  after = writeSuccess156a4After regs global /\
  observations = writeSuccess156a4Observations regs global.
Proof.
  exact (segment_156a4_mstatus_covered regs global observations after).
Qed.

Print Assumptions segment_156a4_mstatus_covered.
Print Assumptions segment_156a4_covered.
