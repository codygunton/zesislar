From Coq Require Import Lists.List.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Theorem writeSuccessWithdrawalsRecordedRunPositionEdges count before segments
    after :
  WriteSuccessWithdrawalsRecordedRun count before segments after ->
  exists states,
    length states = S count /\
    nth_error states 0 = Some before /\
    nth_error states count = Some after /\
    WriteSuccessWithdrawalsPositionEdges segments states.
Proof.
  revert before segments after.
  induction count as [|count IH]; intros before segments after Hrecorded.
  - destruct Hrecorded as (Hrun & HafterLog).
    destruct before as [beforeMachine beforeLog].
    destruct after as [afterMachine afterLog].
    cbn in Hrun, HafterLog |- *.
    inversion Hrun; subst.
    exists [(afterMachine, beforeLog)].
    split; first reflexivity.
    split; first reflexivity.
    split.
    + cbn [flattenMicroObservations segmentRecords]. rewrite app_nil_r.
      reflexivity.
    + exact I.
  - destruct before as [beforeMachine beforeLog].
    destruct Hrecorded as (Hrun & HafterLog).
    cbn in Hrun, HafterLog.
    inversion Hrun as
      [|? beforeMachine' observations middle segmentsTail machineAfter'
        Hsegment Hrest]; subst.
    set (middleLog := beforeLog ++ segmentRecords beforeMachine observations).
    set (middleState := (middle, middleLog)).
    assert (Hfirst : WriteSuccessWithdrawalsRecordedRun 1
        (beforeMachine, beforeLog) [observations] middleState).
    { unfold middleState, middleLog.
      apply writeSuccessWithdrawalsRecordedRunOne. exact Hsegment. }
    assert (Htail : WriteSuccessWithdrawalsRecordedRun count middleState
        segmentsTail (fst after, snd after)).
    { split; first exact Hrest.
      unfold middleState, middleLog. cbn.
      cbn [flattenMicroObservations] in HafterLog.
      rewrite (segmentRecords_app beforeMachine observations middle
        (flattenMicroObservations segmentsTail)) in HafterLog.
      - rewrite HafterLog. apply app_assoc.
      - apply islaInstructionSegmentCorrespondence. exact Hsegment. }
    destruct (IH middleState segmentsTail (fst after, snd after) Htail) as
      (tailStates & Hlength & Hstart & Hend & Hedges).
    exists ((beforeMachine, beforeLog) :: tailStates).
    split; first (cbn; rewrite Hlength; reflexivity).
    split; first reflexivity.
    split.
    + cbn. rewrite (surjective_pairing after). exact Hend.
    + destruct tailStates as [|tailHead tailStates]; first discriminate.
      cbn in Hstart. injection Hstart as ->.
      cbn. split; first exact Hfirst. exact Hedges.
Qed.

Print Assumptions writeSuccessWithdrawalsRecordedRunPositionEdges.
