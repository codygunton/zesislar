From Coq Require Import Lia Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdgesJoin.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.

Local Lemma nth_error_firstn_positioned {A} (values : list A) count index :
  (index < count)%nat ->
  nth_error (firstn count values) index = nth_error values index.
Proof.
  revert count index. induction values as [|value values IH].
  - intros count index Hindex. destruct count; reflexivity.
  - intros count index Hindex. destruct count; first lia.
    destruct index; first reflexivity. cbn. apply IH. lia.
Qed.

Definition WriteSuccessWithdrawalsPositionedPath remaining start segments states
    first last : Prop :=
  length states = S (length segments) /\
  WriteSuccessWithdrawalsPositionEdges segments states /\
  nth_error states 0 = Some first /\
  nth_error states (length segments) = Some last /\
  forall offset stateAt,
    (offset < length segments)%nat ->
    nth_error states offset = Some stateAt ->
    writeSuccessWithdrawalsPositionState remaining (start + offset) stateAt.

Lemma writeSuccessWithdrawalsPositionedPathJoin remaining start firstSegments
    firstStates first shared secondSegments secondStates last :
  WriteSuccessWithdrawalsPositionedPath remaining start firstSegments firstStates
    first shared ->
  WriteSuccessWithdrawalsPositionedPath remaining
    (start + length firstSegments) secondSegments secondStates shared last ->
  exists states,
    WriteSuccessWithdrawalsPositionedPath remaining start
      (firstSegments ++ secondSegments) states first last.
Proof.
  intros Hfirst Hsecond.
  unfold WriteSuccessWithdrawalsPositionedPath in Hfirst, Hsecond |- *.
  destruct Hfirst as
    (HfirstLength & HfirstEdges & HfirstStart & HfirstEnd & HfirstFacts).
  destruct Hsecond as
    (HsecondLength & HsecondEdges & HsecondStart & HsecondEnd & HsecondFacts).
  destruct (writeSuccessWithdrawalsPositionEdgesJoin firstSegments firstStates
    secondSegments secondStates shared HfirstEdges HsecondEdges HfirstEnd
    HsecondStart) as (states & Hstates & Hlength & Hedges).
  have HprefixLength :
      length (firstn (length firstSegments) firstStates) =
        length firstSegments.
  { rewrite firstn_length. rewrite HfirstLength. lia. }
  exists states.
  split; first exact Hlength.
  split; first exact Hedges.
  split.
  - destruct firstSegments as [|firstObservation firstSegments].
    + cbn in HfirstStart, HfirstEnd, Hstates |- *.
      rewrite HfirstStart in HfirstEnd. injection HfirstEnd as <-.
      rewrite Hstates. exact HsecondStart.
    + rewrite Hstates. rewrite nth_error_app1.
      * rewrite nth_error_firstn_positioned; first exact HfirstStart. cbn. lia.
      * rewrite HprefixLength. cbn. lia.
  - split.
    + rewrite Hstates. rewrite app_length. rewrite nth_error_app2.
      * rewrite HprefixLength.
        replace (length firstSegments + length secondSegments -
          length firstSegments)%nat with (length secondSegments) by lia.
        exact HsecondEnd.
      * rewrite HprefixLength. lia.
    + intros offset stateAt Hoffset Hnth.
      rewrite Hstates in Hnth.
      destruct (Nat.lt_ge_cases offset (length firstSegments)) as
        [HinsideFirst|HinsideSecond].
      * rewrite nth_error_app1 in Hnth; last (rewrite HprefixLength; assumption).
        rewrite nth_error_firstn_positioned in Hnth; last assumption.
        eapply HfirstFacts; eassumption.
      * rewrite nth_error_app2 in Hnth;
          last (rewrite HprefixLength; assumption).
        rewrite HprefixLength in Hnth.
        have Hposition := HsecondFacts
          (offset - length firstSegments)%nat stateAt
          ltac:(rewrite app_length in Hoffset; lia) Hnth.
        replace
          (start + length firstSegments +
            (offset - length firstSegments))%nat
          with (start + offset)%nat in Hposition by lia.
        exact Hposition.
Qed.

Print Assumptions writeSuccessWithdrawalsPositionedPathJoin.
