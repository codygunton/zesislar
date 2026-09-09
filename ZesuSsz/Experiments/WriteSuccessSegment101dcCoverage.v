(* Generated from the pinned return trace shape. *)
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101dc.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101dc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101dcCoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101dcCoverageSuffixFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101dcCoverageSuffixSecond.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101dcCoverageSuffixWrite.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101dcCoverageDone.

Lemma segment_101dc_covered regs global (ra : bv 64) observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101dc)) ->
  regs !! "x1" = Some (RVal_Bits ra) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101dc = Some a101dc ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess101dcAlignment = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101dcBefore regs global)
    observations after ->
  after = writeSuccess101dcAfter regs global ra /\
  observations = writeSuccess101dcObservations regs global ra.
Proof.
  intros Hpc Hx1 Hcode Hmstatus Halign Hsegment.
  destruct (segment_101dc_prefix8_covered regs global ra observations after
    Hpc Hx1 Hmstatus Halign Hsegment) as
    (done & labels & spawned & prefix8 & Hprefix8 & Hnil & Hdone & Hend & Hobs).
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (segment_101dc_suffix_first_covered regs global ra prefix8 done
    Hprefix8 Hnil HdoneNb) as (prefix9 & Hprefix9 & Hobs8).
  destruct (segment_101dc_suffix_second_covered regs global ra prefix9 done
    Hprefix9 Hnil HdoneNb) as (prefix10 & Hprefix10 & Hobs9).
  destruct (segment_101dc_suffix_write_covered regs global ra prefix10 done
    Hpc Hprefix10 Hnil HdoneNb) as (prefix11 & Hprefix11 & Hobs10).
  destruct (segment_101dc_done_covered regs global ra prefix11 done labels
    spawned after Hprefix11 Hnil Hdone) as (Hafter & HobsDone).
  split; first exact Hafter.
  rewrite writeSuccess101dcObservationsSplit.
  rewrite Hobs. rewrite Hobs8. rewrite Hobs9. rewrite Hobs10.
  unfold writeSuccess101dcTailObservations.
  rewrite !app_assoc. cbn. rewrite HobsDone. reflexivity.
Qed.

Print Assumptions segment_101dc_covered.
