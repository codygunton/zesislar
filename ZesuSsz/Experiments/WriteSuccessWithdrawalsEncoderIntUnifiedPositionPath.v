From Coq Require Import Lia Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderActualPositionsFrom15694.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdgesJoin.

Import ListNotations.

Local Lemma nth_error_firstn_encoder {A} (values : list A) count index :
  (index < count)%nat ->
  nth_error (firstn count values) index = nth_error values index.
Proof.
  revert count index. induction values as [|value values IH];
    intros count index Hindex.
  - destruct count; first lia. reflexivity.
  - destruct count; first lia. destruct index; first reflexivity.
    cbn. apply IH. lia.
Qed.

Theorem writeSuccessWithdrawalsEncoderIntUnifiedPositionPath remaining start
    (value sp returnAddress : bv 64) (scratch : list (bv 8))
    (memoryFrame : mem_map) (priorLog : list WriteSuccessWithdrawalsRecord)
    (state : WriteSuccessWithdrawalsConcreteState)
    (segments : list (list IslaMicroObservation))
    (after : WriteSuccessWithdrawalsConcreteState) :
  WriteSuccessWithdrawalsEncoderActualPositionPackage remaining start value sp
    returnAddress scratch memoryFrame priorLog state segments after ->
  exists regs global states,
    state.1 = writeSuccess15d10Before regs global /\
    after =
      (writeSuccessWithdrawalsEncoderIntEndpoint regs global sp returnAddress value,
       priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
         returnAddress value) /\
    length states = 16%nat /\
    nth_error states 0 = Some state /\
    nth_error states 15 = Some after /\
    WriteSuccessWithdrawalsPositionEdges segments states /\
    forall offset stateAt,
      (offset < 15)%nat ->
      nth_error states offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining (start + offset) stateAt.
Proof.
  intros Hpackage.
  unfold WriteSuccessWithdrawalsEncoderActualPositionPackage in Hpackage.
  destruct Hpackage as (regs & global & Hentry & Hafter & Hinv & Hrun &
    prefix & output & suffix & prefixStates & outputStates & suffixStates &
    Hsegments & HprefixLength & HoutputLength & HsuffixLength & Hstart &
    HprefixOutput & HoutputSuffix & Hend & HprefixEdges & HoutputEdges &
    HsuffixEdges & HprefixFacts & HoutputFacts & HsuffixFacts).
  have HprefixSegments := writeSuccessWithdrawalsPositionEdgesLength _ _
    HprefixEdges.
  have HoutputSegments := writeSuccessWithdrawalsPositionEdgesLength _ _
    HoutputEdges.
  have HsuffixSegments := writeSuccessWithdrawalsPositionEdgesLength _ _
    HsuffixEdges.
  have HprefixCount : length prefix = 7%nat.
  { rewrite HprefixLength in HprefixSegments. cbn in HprefixSegments. lia. }
  have HoutputCount : length output = 5%nat.
  { rewrite HoutputLength in HoutputSegments. cbn in HoutputSegments. lia. }
  have HsuffixCount : length suffix = 3%nat.
  { rewrite HsuffixLength in HsuffixSegments. cbn in HsuffixSegments. lia. }
  have HprefixEndSome : exists shared,
      nth_error prefixStates 7 = Some shared.
  { destruct (nth_error prefixStates 7) eqn:Hnth.
    - exists p. reflexivity.
    - exfalso. apply (proj2 (nth_error_Some prefixStates 7)).
      + rewrite HprefixLength. lia.
      + exact Hnth. }
  destruct HprefixEndSome as (shared0 & HprefixEnd).
  have HoutputStart : nth_error outputStates 0 = Some shared0 by
    (rewrite <- HprefixOutput; exact HprefixEnd).
  destruct (writeSuccessWithdrawalsPositionEdgesJoin prefix prefixStates output
    outputStates shared0 HprefixEdges HoutputEdges
    ltac:(rewrite HprefixCount; exact HprefixEnd) HoutputStart) as
    (prefixOutputStates & HprefixOutputStates & HprefixOutputLength &
     HprefixOutputEdges).
  have HoutputEndSome : exists shared,
      nth_error outputStates 5 = Some shared.
  { destruct (nth_error outputStates 5) eqn:Hnth.
    - exists p. reflexivity.
    - exfalso. apply (proj2 (nth_error_Some outputStates 5)).
      + rewrite HoutputLength. lia.
      + exact Hnth. }
  destruct HoutputEndSome as (shared1 & HoutputEnd).
  have HsuffixStart : nth_error suffixStates 0 = Some shared1 by
    (rewrite <- HoutputSuffix; exact HoutputEnd).
  have HprefixOutputEnd :
      nth_error prefixOutputStates (length (prefix ++ output)) = Some shared1.
  { rewrite HprefixOutputStates. rewrite app_length. rewrite HprefixCount. rewrite HoutputCount.
    rewrite nth_error_app2.
    - replace (12 - length (firstn 7 prefixStates))%nat with 5%nat.
      + exact HoutputEnd.
      + rewrite firstn_length. rewrite HprefixLength. lia.
    - rewrite firstn_length. rewrite HprefixLength. lia. }
  destruct (writeSuccessWithdrawalsPositionEdgesJoin (prefix ++ output)
    prefixOutputStates suffix suffixStates shared1 HprefixOutputEdges HsuffixEdges
    HprefixOutputEnd HsuffixStart) as
    (states & Hstates & Hlength & Hedges).
  exists regs, global, states.
  split; first exact Hentry.
  split; first exact Hafter.
  split.
  { rewrite Hlength. rewrite app_length. rewrite app_length. rewrite HprefixCount. rewrite HoutputCount. rewrite HsuffixCount. reflexivity. }
  split.
  { rewrite Hstates. rewrite nth_error_app1.
    - rewrite nth_error_firstn_encoder.
      + rewrite HprefixOutputStates. rewrite nth_error_app1.
        * rewrite nth_error_firstn_encoder; first exact Hstart. rewrite HprefixCount. lia.
        * rewrite firstn_length. rewrite HprefixCount. rewrite HprefixLength. lia.
      + rewrite app_length. rewrite HprefixCount. rewrite HoutputCount. lia.
    - rewrite firstn_length. rewrite HprefixOutputLength. rewrite app_length.
      rewrite HprefixCount. rewrite HoutputCount. lia. }
  split.
  { rewrite Hstates. rewrite app_length. rewrite HprefixCount. rewrite HoutputCount.
    rewrite nth_error_app2.
    - replace (15 - length (firstn 12 prefixOutputStates))%nat with 3%nat.
      + exact Hend.
      + rewrite firstn_length. rewrite HprefixOutputLength. rewrite app_length. rewrite HprefixCount. rewrite HoutputCount. lia.
    - rewrite firstn_length. rewrite HprefixOutputLength. rewrite app_length. rewrite HprefixCount. rewrite HoutputCount. lia. }
  split; first (rewrite Hsegments; exact Hedges).
  intros offset stateAt Hoffset Hnth.
  rewrite Hstates in Hnth.
  have HfirstLength : length (firstn (length (prefix ++ output))
      prefixOutputStates) = 12%nat.
  { rewrite firstn_length. rewrite HprefixOutputLength. rewrite app_length. rewrite HprefixCount. rewrite HoutputCount. lia. }
  destruct (Nat.lt_ge_cases offset 12) as [HbeforeSuffix|Hsuffix].
  - rewrite nth_error_app1 in Hnth; last (rewrite HfirstLength; exact HbeforeSuffix).
    rewrite nth_error_firstn_encoder in Hnth;
      last (rewrite app_length; rewrite HprefixCount; rewrite HoutputCount; lia).
    rewrite HprefixOutputStates in Hnth.
    have HprefixPartLength : length (firstn (length prefix) prefixStates) = 7%nat.
    { rewrite HprefixCount. rewrite firstn_length. rewrite HprefixLength. lia. }
    destruct (Nat.lt_ge_cases offset 7) as [HbeforeOutput|Houtput].
    + rewrite nth_error_app1 in Hnth;
        last (rewrite HprefixPartLength; exact HbeforeOutput).
      rewrite HprefixCount in Hnth.
      rewrite nth_error_firstn_encoder in Hnth; last exact HbeforeOutput.
      apply HprefixFacts with (offset := offset); assumption.
    + rewrite nth_error_app2 in Hnth;
        last (rewrite HprefixPartLength; exact Houtput).
      rewrite HprefixPartLength in Hnth.
      replace (start + offset)%nat with
        (start + (7 + (offset - 7)))%nat by lia.
      apply HoutputFacts with (offset := (offset - 7)%nat).
      * lia.
      * exact Hnth.
  - rewrite nth_error_app2 in Hnth;
      last (rewrite HfirstLength; exact Hsuffix).
    rewrite HfirstLength in Hnth.
    replace (start + offset)%nat with
      (start + (12 + (offset - 12)))%nat by lia.
    apply HsuffixFacts with (offset := (offset - 12)%nat).
    + lia.
    + exact Hnth.
Qed.

Print Assumptions writeSuccessWithdrawalsEncoderIntUnifiedPositionPath.
