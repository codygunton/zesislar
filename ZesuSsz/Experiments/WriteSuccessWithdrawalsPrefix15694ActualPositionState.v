From Coq Require Import Lia Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Positions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694PositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Theorem writeSuccessWithdrawalsPrefix15694ActualPositionStates args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state segments
    after :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  WriteSuccessWithdrawalsRecordedRun 5 state segments after ->
  exists states,
    after = (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog) /\
    length states = 6%nat /\
    nth_error states 0 = Some state /\
    nth_error states 5 = Some after /\
    WriteSuccessWithdrawalsPositionEdges segments states /\
    forall offset stateAt,
      (offset < 5)%nat ->
      nth_error states offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining offset stateAt.
Proof.
  intros Hinv Hrecorded.
  destruct (writeSuccessWithdrawalsPrefix15694PositionsExact args sp pointer
    base total processed (S remaining) withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state segments
    after Hinv Hrecorded) as
    (o0 & o1 & o2 & o3 & o4 & Hsegments & Hafter & Hr0 & Hr1 & Hr2 & Hr3 &
     Hr4).
  destruct (writeSuccessWithdrawalsPrefix15694PositionStates args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state Hinv) as
    (Hp0 & Hp1 & Hp2 & Hp3 & Hp4).
  exists [state;
    (writeSuccessWithdrawalsPrefixState98 state.1 sp, priorLog);
    (writeSuccessWithdrawalsPrefixState9c state.1 sp, priorLog);
    (writeSuccessWithdrawalsPrefixStatea0 state.1 sp pointer, priorLog);
    (writeSuccessWithdrawalsPrefixStatea4 state.1 sp pointer, priorLog);
    after].
  split; first exact Hafter.
  split; first reflexivity.
  split; first reflexivity.
  split; first reflexivity.
  split.
  { rewrite Hsegments Hafter. cbn.
    split; first exact Hr0.
    split; first exact Hr1.
    split; first exact Hr2.
    split; first exact Hr3.
    split; first exact Hr4.
    exact I. }
  intros offset stateAt Hoffset Hnth.
  destruct offset as [|[|[|[|[|offset]]]]]; try lia; cbn in Hnth;
    injection Hnth as <-; assumption.
Qed.

Print Assumptions writeSuccessWithdrawalsPrefix15694ActualPositionStates.
