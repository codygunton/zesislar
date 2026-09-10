From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156dc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e4.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156dcLoopTailPositions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessWithdrawals156dcLoopTailRecordedPositionPath regs global
    (pointer : bv 64) remaining priorLog segments after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156dc)) ->
  regs !! "x8" = Some (RVal_Bits pointer) ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  eval_a_exp regs writeSuccess156dcMstatus = Some (Val_Bool true) ->
  writeSuccessWithdrawalsInstructionTable global ->
  WriteSuccessWithdrawalsRecordedRun 3
    (writeSuccess156dcBefore regs global, priorLog) segments after ->
  after =
    (writeSuccess156e4After (Z_to_bv 64 (Z.of_nat remaining))
      (writeSuccess156e0Regs (writeSuccess156dcRegs regs pointer)
        (Z_to_bv 64 (Z.of_nat (S remaining)))) global,
     priorLog) /\
  segments =
    [writeSuccess156dcObservations regs global pointer;
     writeSuccess156e0Observations (writeSuccess156dcRegs regs pointer) global
       (Z_to_bv 64 (Z.of_nat (S remaining)));
     writeSuccess156e4Observations (Z_to_bv 64 (Z.of_nat remaining))
       (writeSuccess156e0Regs (writeSuccess156dcRegs regs pointer)
         (Z_to_bv 64 (Z.of_nat (S remaining)))) global] /\
  exists states,
    length states = 4%nat /\
    nth_error states 0 =
      Some (writeSuccess156dcBefore regs global, priorLog) /\
    nth_error states 3 = Some after /\
    WriteSuccessWithdrawalsPositionEdges segments states.
Proof.
  intros Hpc Hx8 Hx9 Hmstatus Htable Hrecorded.
  destruct (writeSuccessWithdrawals156dcLoopTailPositionsExact regs global
    pointer remaining priorLog segments after Hpc Hx8 Hx9 Hmstatus Htable
    Hrecorded) as (Hafter & Hsegments).
  destruct (writeSuccessWithdrawalsRecordedRunPositionEdges 3
    (writeSuccess156dcBefore regs global, priorLog) segments after Hrecorded) as
    (states & Hlength & Hstart & Hend & Hedges).
  split; first exact Hafter.
  split; first exact Hsegments.
  exists states. repeat split; assumption.
Qed.

Print Assumptions writeSuccessWithdrawals156dcLoopTailRecordedPositionPath.
