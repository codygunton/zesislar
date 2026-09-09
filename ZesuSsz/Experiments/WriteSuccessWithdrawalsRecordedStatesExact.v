From Coq Require Import Lia Lists.List.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Theorem writeSuccessWithdrawalsRecordedRunStatesExact count before segments after :
  WriteSuccessWithdrawalsRecordedRun count before segments after ->
  exists states,
    length states = S count /\
    nth_error states 0 = Some before /\
    nth_error states count = Some after /\
    (forall position,
      (position < count)%nat ->
      exists observations beforeAt afterAt,
        nth_error segments position = Some observations /\
        nth_error states position = Some beforeAt /\
        nth_error states (S position) = Some afterAt /\
        WriteSuccessWithdrawalsRecordedRun 1 beforeAt [observations] afterAt).
Proof.
  revert before segments after.
  induction count as [|count IH]; intros before segments after Hrecorded.
  - destruct Hrecorded as (Hrun & HafterLog).
    destruct before as [beforeMachine beforeLog].
    destruct after as [afterMachine afterLog].
    cbn in Hrun, HafterLog |- *.
    set (initial := (beforeMachine, beforeLog)).
    inversion Hrun; subst.
    exists [initial].
    unfold initial.
    split; first reflexivity.
    split; first reflexivity.
    split.
    + cbn [flattenMicroObservations segmentRecords].
      rewrite app_nil_r. reflexivity.
    + intros position Hposition. lia.
  - destruct before as [beforeMachine beforeLog].
    destruct Hrecorded as (Hrun & HafterLog).
    cbn in Hrun, HafterLog |- *.
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
    split; first (cbn; lia).
    split; first reflexivity.
    split.
    + cbn. rewrite (surjective_pairing after). exact Hend.
    + intros position Hposition.
      destruct position as [|position].
      * exists observations, (beforeMachine, beforeLog), middleState.
        split; first reflexivity.
        split; first reflexivity.
        split; first (cbn; exact Hstart).
        exact Hfirst.
      * destruct (Hedges position ltac:(lia)) as
          (tailObservations & beforeAt & afterAt & Hobservations & HbeforeAt &
           HafterAt & Hone).
        exists tailObservations, beforeAt, afterAt. cbn.
        split; first exact Hobservations.
        split; first exact HbeforeAt.
        split; first exact HafterAt.
        exact Hone.
Qed.

Print Assumptions writeSuccessWithdrawalsRecordedRunStatesExact.
