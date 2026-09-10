From Coq Require Import Lia Lists.List.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.

Import ListNotations.

Lemma writeSuccessWithdrawalsPositionEdgesJoin firstSegments firstStates
    secondSegments secondStates shared :
  WriteSuccessWithdrawalsPositionEdges firstSegments firstStates ->
  WriteSuccessWithdrawalsPositionEdges secondSegments secondStates ->
  nth_error firstStates (length firstSegments) = Some shared ->
  nth_error secondStates 0 = Some shared ->
  exists states,
    states = firstn (length firstSegments) firstStates ++ secondStates /\
    length states = S (length (firstSegments ++ secondSegments)) /\
    WriteSuccessWithdrawalsPositionEdges
      (firstSegments ++ secondSegments) states.
Proof.
  intros Hfirst Hsecond HfirstEnd HsecondStart.
  pose proof (writeSuccessWithdrawalsPositionEdgesLength _ _ Hfirst) as
    HfirstLength.
  pose proof (writeSuccessWithdrawalsPositionEdgesLength _ _ Hsecond) as
    HsecondLength.
  destruct (nth_error_split firstStates (length firstSegments) HfirstEnd)
    as (firstPrefix & firstSuffix & HfirstStates & HfirstPrefixLength).
  destruct (nth_error_split secondStates 0 HsecondStart)
    as (secondPrefix & secondSuffix & HsecondStates & HsecondPrefixLength).
  subst firstStates secondStates.
  destruct firstSuffix as [|extra firstSuffix].
  2: rewrite app_length in HfirstLength; cbn in HfirstLength;
     rewrite HfirstPrefixLength in HfirstLength; lia.
  destruct secondPrefix as [|extra secondPrefix].
  2: cbn in HsecondPrefixLength; lia.
  exists (firstPrefix ++ shared :: secondSuffix).
  split.
  - rewrite firstn_app. rewrite <- HfirstPrefixLength. rewrite firstn_all.
    replace (length firstPrefix - length firstPrefix)%nat with 0%nat by lia.
    cbn. rewrite app_nil_r. reflexivity.
  - split.
    + rewrite app_length in HsecondLength. cbn in HsecondLength.
      rewrite app_length, app_length. cbn.
      rewrite HfirstPrefixLength. lia.
    + eapply writeSuccessWithdrawalsPositionEdgesApp; eassumption.
Qed.

Print Assumptions writeSuccessWithdrawalsPositionEdgesJoin.
