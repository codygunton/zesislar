From Coq Require Import Lia Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyActualPositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyAfter.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyInduction.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyPositions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdgesJoin.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.

Import ListNotations.
Open Scope Z_scope.

Local Lemma nth_error_firstn_memcpy {A} (values : list A) count index :
  (index < count)%nat ->
  nth_error (firstn count values) index = nth_error values index.
Proof.
  revert count index. induction values as [|value values IH];
    intros count index Hindex.
  - destruct count; first lia. reflexivity.
  - destruct count; first lia. destruct index; first reflexivity.
    cbn. apply IH. lia.
Qed.

Lemma writeSuccessMemcpyBytesPositionStatesLength regs global source destination
    index length bytes priorLog :
  List.length (writeSuccessMemcpyBytesPositionStates regs global source
    destination index length bytes priorLog) = S (7 * List.length bytes).
Proof.
  revert regs global index. induction bytes as [|byte tail IH];
    intros regs global index; first reflexivity.
  cbn [writeSuccessMemcpyBytesPositionStates]. rewrite app_length. cbn.
  rewrite IH. lia.
Qed.

Lemma writeSuccessMemcpyBytesPositionStatesLast regs global source destination
    index length bytes priorLog :
  nth_error (writeSuccessMemcpyBytesPositionStates regs global source
    destination index length bytes priorLog) (7 * List.length bytes) =
  Some (writeSuccessMemcpyBytesAfter regs global source destination index bytes,
    priorLog).
Proof.
  revert regs global index. induction bytes as [|byte tail IH];
    intros regs global index; first reflexivity.
  cbn [writeSuccessMemcpyBytesPositionStates]. rewrite nth_error_app2;
    last (change (7 <= 7 * S (List.length tail))%nat; lia).
  cbn [writeSuccessMemcpyBytePositionPrefixStates].
  replace (7 * S (List.length tail) - 7)%nat with
    (7 * List.length tail)%nat by lia.
  apply IH.
Qed.

Theorem writeSuccessWithdrawalsMemcpyUnifiedPositionPath args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state segments after :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  WriteSuccessWithdrawalsRecordedRun 339
    (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog)
    segments after ->
  exists regs global states,
    writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
      writeSuccess101d4Before regs global /\
    after =
      (writeSuccessWithdrawals156a8State regs global sp pointer current,
       priorLog) /\
    length states = 340%nat /\
    nth_error states 0 = Some
      (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog) /\
    nth_error states 339 = Some after /\
    WriteSuccessWithdrawalsPositionEdges segments states /\
    forall offset stateAt,
      (offset < 339)%nat ->
      nth_error states offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining (5 + offset) stateAt.
Proof.
  intros Hinv Hrun.
  destruct (writeSuccessWithdrawalsMemcpyActualPositionGroups args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state segments
    after Hinv Hrun) as
    (regs & global & returnTrace & obsD4 & loopSegments & obsD8 & obsDc &
     Hentry & Hreturn & Hafter & Hsegments & HrD4 & Hloop & HrD8 & HrDc &
     Hposition5 & HloopPositions & Hposition342 & Hposition343).
  set (start :=
    (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog)).
  set (entryAfter := (writeSuccess101d4After regs global, priorLog)).
  set (loopStates := writeSuccessMemcpyBytesPositionStates
    (writeSuccess101d4Regs regs) global pointer (sp + BV 64 1744)%bv
    (BV 64 0) (BV 64 48) current priorLog).
  set (loopAfter := (writeSuccessMemcpyLoopAfter regs global pointer
    (sp + BV 64 1744)%bv current, priorLog)).
  set (fallthrough :=
    (writeSuccess101d8FallthroughAfter
      (writeSuccessMemcpyLoopAfter regs global pointer
        (sp + BV 64 1744)%bv current).1.(seq_regs)
      (writeSuccessMemcpyEndpointGlobal regs global pointer
        (sp + BV 64 1744)%bv current), priorLog)).
  have Hcurrent : length current = 48%nat by
    (unfold Inv_15694 in Hinv; tauto).
  have HloopLength : length loopStates = 337%nat.
  { unfold loopStates. rewrite writeSuccessMemcpyBytesPositionStatesLength.
    rewrite Hcurrent. reflexivity. }
  have HloopCount : length loopSegments = 336%nat.
  { pose proof (writeSuccessWithdrawalsPositionEdgesLength _ _ Hloop) as
      HedgesLength.
    rewrite HloopLength in HedgesLength.
    lia. }
  have HloopStart : nth_error loopStates 0 = Some entryAfter.
  { unfold loopStates, entryAfter.
    rewrite writeSuccessMemcpyBytesPositionStatesHead. reflexivity. }
  have HloopEnd : nth_error loopStates 336 = Some loopAfter.
  { unfold loopStates, loopAfter, writeSuccessMemcpyLoopAfter.
    replace 336%nat with (7 * length current)%nat by
      (rewrite Hcurrent; reflexivity).
    replace (BV 64 0) with (Z_to_bv 64 0) by (apply bv_eq; reflexivity).
    apply writeSuccessMemcpyBytesPositionStatesLast. }
  have HentryEdges : WriteSuccessWithdrawalsPositionEdges [obsD4]
      [start; entryAfter].
  { cbn. split; first (unfold start, entryAfter; exact HrD4). exact I. }
  destruct (writeSuccessWithdrawalsPositionEdgesJoin [obsD4]
    [start; entryAfter] loopSegments loopStates entryAfter HentryEdges Hloop
    ltac:(reflexivity) HloopStart) as
    (entryLoopStates & HentryLoopStates & HentryLoopLength & HentryLoopEdges).
  have HentryLoopEnd : nth_error entryLoopStates 337 = Some loopAfter.
  { rewrite HentryLoopStates. cbn. exact HloopEnd. }
  have HexitEdges : WriteSuccessWithdrawalsPositionEdges [obsD8]
      [loopAfter; fallthrough].
  { cbn. split; first (unfold loopAfter, fallthrough; exact HrD8). exact I. }
  destruct (writeSuccessWithdrawalsPositionEdgesJoin
    ([obsD4] ++ loopSegments) entryLoopStates [obsD8]
    [loopAfter; fallthrough] loopAfter HentryLoopEdges HexitEdges
    ltac:(rewrite app_length; cbn; rewrite HloopCount; exact HentryLoopEnd)
    ltac:(reflexivity)) as
    (throughExitStates & HthroughExitStates & HthroughExitLength &
     HthroughExitEdges).
  have HthroughExitEnd : nth_error throughExitStates 338 = Some fallthrough.
  { rewrite HthroughExitStates. rewrite nth_error_app2.
    - replace (338 - length
        (firstn (length ([obsD4] ++ loopSegments)) entryLoopStates))%nat
        with 1%nat.
      + reflexivity.
      + rewrite firstn_length. rewrite Nat.min_l;
          last (rewrite HentryLoopLength; lia).
        rewrite app_length. cbn. rewrite HloopCount. lia.
    - rewrite firstn_length. rewrite Nat.min_l;
        last (rewrite HentryLoopLength; lia).
      rewrite app_length. cbn. rewrite HloopCount. lia. }
  have HreturnEdges : WriteSuccessWithdrawalsPositionEdges [obsDc]
      [fallthrough; after].
  { cbn. split; first (unfold fallthrough; exact HrDc). exact I. }
  destruct (writeSuccessWithdrawalsPositionEdgesJoin
    (([obsD4] ++ loopSegments) ++ [obsD8]) throughExitStates [obsDc]
    [fallthrough; after] fallthrough HthroughExitEdges HreturnEdges
    ltac:(rewrite !app_length; cbn; rewrite HloopCount; exact HthroughExitEnd)
    ltac:(reflexivity)) as
    (states & Hstates & HstatesLength & Hedges).
  have HentryPrefixLength : length
      (firstn (length ([obsD4] ++ loopSegments)) entryLoopStates) = 337%nat.
  { rewrite firstn_length. rewrite Nat.min_l;
      last (rewrite HentryLoopLength; lia).
    rewrite app_length. cbn. rewrite HloopCount. reflexivity. }
  have HthroughPrefixLength : length
      (firstn (length (([obsD4] ++ loopSegments) ++ [obsD8]))
        throughExitStates) = 338%nat.
  { rewrite firstn_length. rewrite Nat.min_l;
      last (rewrite HthroughExitLength; lia).
    rewrite !app_length. cbn. rewrite HloopCount. reflexivity. }
  exists regs, global, states.
  split; first exact Hentry.
  split; first exact Hafter.
  split.
  { rewrite HstatesLength. rewrite !app_length. rewrite HloopCount. reflexivity. }
  split.
  { rewrite Hstates.
    rewrite nth_error_app1.
    - rewrite nth_error_firstn_memcpy; last (rewrite !app_length; cbn; lia).
      rewrite HthroughExitStates.
      rewrite nth_error_app1.
      + rewrite nth_error_firstn_memcpy; last (rewrite app_length; cbn; lia).
        rewrite HentryLoopStates. reflexivity.
      + rewrite HentryPrefixLength. lia.
    - rewrite HthroughPrefixLength. lia. }
  split.
  { rewrite Hstates.
    rewrite nth_error_app2.
    - rewrite HthroughPrefixLength. reflexivity.
    - rewrite HthroughPrefixLength. lia. }
  split.
  { rewrite Hsegments.
    replace ([obsD4] ++ loopSegments ++ [obsD8; obsDc]) with
      ((([obsD4] ++ loopSegments) ++ [obsD8]) ++ [obsDc]) by
      (rewrite <- app_assoc; reflexivity).
    exact Hedges. }
  intros offset stateAt Hoffset Hnth.
  rewrite Hstates in Hnth.
  destruct (Nat.lt_ge_cases offset 338) as [HbeforeReturn|Hfallthrough].
  - rewrite nth_error_app1 in Hnth;
      last (rewrite HthroughPrefixLength; exact HbeforeReturn).
    rewrite nth_error_firstn_memcpy in Hnth;
      last (rewrite !app_length; cbn; rewrite HloopCount; exact HbeforeReturn).
    rewrite HthroughExitStates in Hnth.
    destruct (Nat.lt_ge_cases offset 337) as [HbeforeExit|Hexit].
    + rewrite nth_error_app1 in Hnth;
        last (rewrite HentryPrefixLength; exact HbeforeExit).
      rewrite nth_error_firstn_memcpy in Hnth;
        last (rewrite app_length; cbn; rewrite HloopCount; exact HbeforeExit).
      rewrite HentryLoopStates in Hnth.
      destruct offset as [|offset].
      * cbn in Hnth. injection Hnth as <-. exact Hposition5.
      * cbn in Hnth.
        apply HloopPositions with (offset := offset); try lia. exact Hnth.
    + have Hoff : offset = 337%nat by lia. subst offset.
      rewrite nth_error_app2 in Hnth; last (rewrite HentryPrefixLength; lia).
      rewrite HentryPrefixLength in Hnth. cbn in Hnth. injection Hnth as <-.
      exact Hposition342.
  - have Hoff : offset = 338%nat by lia. subst offset.
    rewrite nth_error_app2 in Hnth; last (rewrite HthroughPrefixLength; lia).
    rewrite HthroughPrefixLength in Hnth. cbn in Hnth. injection Hnth as <-.
    exact Hposition343.
Qed.

Print Assumptions writeSuccessMemcpyBytesPositionStatesLength.
Print Assumptions writeSuccessMemcpyBytesPositionStatesLast.
Print Assumptions writeSuccessWithdrawalsMemcpyUnifiedPositionPath.
