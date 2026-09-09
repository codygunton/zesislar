(* Generated from the pinned return trace shape. *)
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_01.a101a0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0CoverageSuffixFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0CoverageSuffixSecond.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0CoverageSuffixWrite.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0CoverageDone.

Lemma segment_101a0_covered regs global (ra : bv 64) observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101a0)) ->
  regs !! "x1" = Some (RVal_Bits ra) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101a0 = Some a101a0 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess101a0Alignment = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101a0Before regs global)
    observations after ->
  after = writeSuccess101a0After regs global ra /\
  observations = writeSuccess101a0Observations regs global ra.
Proof.
  intros Hpc Hx1 Hcode Hmstatus Halign Hsegment.
  destruct (segment_101a0_prefix8_covered regs global ra observations after
    Hpc Hx1 Hmstatus Halign Hsegment) as
    (done & labels & spawned & prefix8 & Hprefix8 & Hnil & Hdone & Hend & Hobs).
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (segment_101a0_suffix_first_covered regs global ra prefix8 done
    Hprefix8 Hnil HdoneNb) as (prefix9 & Hprefix9 & Hobs8).
  destruct (segment_101a0_suffix_second_covered regs global ra prefix9 done
    Hprefix9 Hnil HdoneNb) as (prefix10 & Hprefix10 & Hobs9).
  destruct (segment_101a0_suffix_write_covered regs global ra prefix10 done
    Hpc Hprefix10 Hnil HdoneNb) as (prefix11 & Hprefix11 & Hobs10).
  destruct (segment_101a0_done_covered regs global ra prefix11 done labels
    spawned after Hprefix11 Hnil Hdone) as (Hafter & HobsDone).
  split; first exact Hafter.
  rewrite writeSuccess101a0ObservationsSplit.
  rewrite Hobs. rewrite Hobs8. rewrite Hobs9. rewrite Hobs10.
  unfold writeSuccess101a0TailObservations.
  rewrite !app_assoc. cbn. rewrite HobsDone. reflexivity.
Qed.

Print Assumptions segment_101a0_covered.
