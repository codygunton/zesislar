(* Generated from the pinned return trace shape. *)
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d34.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d34.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d34CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d34CoverageSuffixFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d34CoverageSuffixSecond.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d34CoverageSuffixWrite.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d34CoverageDone.

Lemma segment_15d34_covered regs global (ra : bv 64) observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d34)) ->
  regs !! "x1" = Some (RVal_Bits ra) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d34 = Some a15d34 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d34Alignment = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d34Before regs global)
    observations after ->
  after = writeSuccess15d34After regs global ra /\
  observations = writeSuccess15d34Observations regs global ra.
Proof.
  intros Hpc Hx1 Hcode Hmstatus Halign Hsegment.
  destruct (segment_15d34_prefix8_covered regs global ra observations after
    Hpc Hx1 Hmstatus Halign Hsegment) as
    (done & labels & spawned & prefix8 & Hprefix8 & Hnil & Hdone & Hend & Hobs).
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (segment_15d34_suffix_first_covered regs global ra prefix8 done
    Hprefix8 Hnil HdoneNb) as (prefix9 & Hprefix9 & Hobs8).
  destruct (segment_15d34_suffix_second_covered regs global ra prefix9 done
    Hprefix9 Hnil HdoneNb) as (prefix10 & Hprefix10 & Hobs9).
  destruct (segment_15d34_suffix_write_covered regs global ra prefix10 done
    Hpc Hprefix10 Hnil HdoneNb) as (prefix11 & Hprefix11 & Hobs10).
  destruct (segment_15d34_done_covered regs global ra prefix11 done labels
    spawned after Hprefix11 Hnil Hdone) as (Hafter & HobsDone).
  split; first exact Hafter.
  rewrite writeSuccess15d34ObservationsSplit.
  rewrite Hobs. rewrite Hobs8. rewrite Hobs9. rewrite Hobs10.
  unfold writeSuccess15d34TailObservations.
  rewrite !app_assoc. cbn. rewrite HobsDone. reflexivity.
Qed.

Print Assumptions segment_15d34_covered.
