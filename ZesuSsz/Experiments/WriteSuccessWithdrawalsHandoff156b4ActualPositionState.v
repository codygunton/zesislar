From Coq Require Import Lia Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b4Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b8Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4PositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderPositions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionStateLog.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedEdgeEndpoint.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Theorem writeSuccessWithdrawals156b4ActualPositionStates args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs
    global segments after :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
    withdrawal = writeSuccess15d10Before regs global ->
  WriteSuccessWithdrawalsRecordedRun 3
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal,
     priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
       (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal))
    segments after ->
  after =
    (writeSuccessWithdrawalsSecondEncoderEntry regs global sp withdrawal,
     priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
       (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)) /\
  exists states,
    length states = 4%nat /\
    nth_error states 0 = Some
      (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal,
       priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
         (Z_to_bv 64 0x156b4)
         (writeSuccessWithdrawalsIndexValue withdrawal)) /\
    nth_error states 3 = Some after /\
    WriteSuccessWithdrawalsPositionEdges segments states /\
    forall offset stateAt,
      (offset < 3)%nat ->
      nth_error states offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining (362 + offset) stateAt.
Proof.
  intros Hinv Hprefix Hentry Hrecorded.
  destruct (writeSuccessWithdrawals156b4SecondEncoderPositionPath args sp
    pointer base total processed (S remaining) withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs global segments after Hinv Hprefix Hentry Hrecorded) as
    (Hafter & states & Hlength & Hstart & Hend & Hedges).
  split; first exact Hafter.
  have Hsemantic := writeSuccessWithdrawals156b4HandoffPositionStates args sp
    pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs global Hinv Hprefix Hentry.
  destruct (writeSuccessWithdrawalsFirstEncoderEndpointDirectFacts args sp
    pointer base total processed (S remaining) withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs global Hinv Hprefix Hentry) as
    (mstatusBits & satp & oldDest & oldX1 & Hpc & Hsp & Hmstatus & Hsatp &
     Hdest & Hx1 & Hsys & HmstatusEval & Haligned & Hlower & Hupper & Hread &
     HtableEnd).
  have HfirstInv := writeSuccessWithdrawals156a8EncoderIntInv args sp pointer
    base total processed (S remaining) withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    Hinv Hprefix.
  rewrite Hentry in HfirstInv.
  have Htable : writeSuccessWithdrawalsInstructionTable global by
    (unfold Inv_encoder_int in HfirstInv; cbn in HfirstInv; tauto).
  have Hbefore := writeSuccessWithdrawalsFirstEncoderEndpointBefore regs global
    sp withdrawal Htable.
  have HmachineRun := proj1 Hrecorded.
  rewrite Hbefore in HmachineRun.
  inversion HmachineRun as
    [|? ? observations0 middle0 segments0 machineAfter0 Hseg0 Hrun0]; subst.
  inversion Hrun0 as
    [|? ? observations1 middle1 segments1 machineAfter1 Hseg1 Hrun1]; subst.
  destruct (segment_156b4_covered
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).2
    mstatusBits sp satp (writeSuccessWithdrawalsValidatorValue withdrawal)
    oldDest observations0 middle0 Hpc Hsp Hmstatus Hsatp Hdest Hsys
    HmstatusEval Haligned Hlower Hupper Hread
    (HtableEnd 0x156b4 _ ltac:(cbn; tauto))
    (HtableEnd 0x156b8 _ ltac:(cbn; tauto)) Hseg0) as (Hmiddle0 & Hobs0).
  subst middle0 observations0.
  have Hpc1 : writeSuccess156b4Regs
      (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
      (writeSuccessWithdrawalsValidatorValue withdrawal) !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x156b8)).
  { unfold writeSuccess156b4Regs. rewrite lookup_insert.
    rewrite writeSuccess156b4NextPcExact. reflexivity. }
  have Hx1_1 : writeSuccess156b4Regs
      (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
      (writeSuccessWithdrawalsValidatorValue withdrawal) !! "x1" = Some oldX1.
  { rewrite writeSuccess156b4RegsLookupOther; try discriminate. exact Hx1. }
  have Hmstatus1 : eval_a_exp (writeSuccess156b4Regs
      (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
      (writeSuccessWithdrawalsValidatorValue withdrawal))
      writeSuccess15694Mstatus = Some (Val_Bool true).
  { unfold writeSuccess156b4Regs. cbn.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate. exact HmstatusEval. }
  destruct (segment_156b8_mstatus_covered
    (writeSuccess156b4Regs
      (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
      (writeSuccessWithdrawalsValidatorValue withdrawal))
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).2
    oldX1 observations1 middle1 Hpc1 Hx1_1
    (HtableEnd 0x156b8 _ ltac:(cbn; tauto))
    (HtableEnd 0x156bc _ ltac:(cbn; tauto)) Hmstatus1 Hseg1) as
    (Hmiddle1 & Hobs1).
  subst middle1 observations1.
  exists states. repeat split; try assumption.
  intros offset stateAt Hoffset Hnth.
  destruct offset as [|[|[|offset]]]; try lia.
  - rewrite Hstart in Hnth. injection Hnth as <-.
    eapply writeSuccessWithdrawalsPositionStateLog. exact (proj1 Hsemantic).
  - destruct stateAt as [stateMachine stateLog].
    destruct (writeSuccessWithdrawalsActualRecordedSuccessor _ states 0
      (writeSuccess156b4Observations
        (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
        (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).2
        mstatusBits sp satp (writeSuccessWithdrawalsValidatorValue withdrawal))
      (stateMachine, stateLog)
      {| microLabels := [];
         microAfter := writeSuccessWithdrawalsFirstEncoderEndpoint regs global
           sp withdrawal |} Hedges ltac:(reflexivity) Hnth) as (labels & Hlast).
    unfold writeSuccess156b4Observations in Hlast.
    rewrite writeSuccessWithdrawalsLastAppSingleton in Hlast.
    have Hmachine := f_equal microAfter Hlast. cbn in Hmachine.
    subst stateMachine.
    eapply writeSuccessWithdrawalsPositionStateLog. exact (proj1 (proj2 Hsemantic)).
  - destruct stateAt as [stateMachine stateLog].
    destruct (writeSuccessWithdrawalsActualRecordedSuccessor _ states 1
      (writeSuccess156b8Observations
        (writeSuccess156b4Regs
          (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
          (writeSuccessWithdrawalsValidatorValue withdrawal))
        (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).2)
      (stateMachine, stateLog)
      {| microLabels := [];
         microAfter := writeSuccessWithdrawalsFirstEncoderEndpoint regs global
           sp withdrawal |} Hedges ltac:(reflexivity) Hnth) as (labels & Hlast).
    unfold writeSuccess156b8Observations in Hlast.
    rewrite writeSuccessWithdrawalsLastAppSingleton in Hlast.
    have Hmachine := f_equal microAfter Hlast. cbn in Hmachine.
    subst stateMachine.
    eapply writeSuccessWithdrawalsPositionStateLog.
    exact (proj2 (proj2 Hsemantic)).
Qed.

Print Assumptions writeSuccessWithdrawals156b4ActualPositionStates.
