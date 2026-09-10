From Coq Require Import Lia Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankIndexedRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Theorem writeSuccessWithdrawalsIndexedRunFromStateEquations remaining before
    segments states :
  length states = 411%nat ->
  nth_error states 0 = Some before ->
  (forall position,
    (position < 410)%nat ->
    exists observations beforeAt afterAt,
      nth_error segments position = Some observations /\
      nth_error states position = Some beforeAt /\
      nth_error states (S position) = Some afterAt /\
      WriteSuccessWithdrawalsRecordedRun 1 beforeAt [observations] afterAt) ->
  (forall position stateAt,
    (position < 409)%nat ->
    nth_error states position = Some stateAt ->
    writeSuccessWithdrawalsPositionState remaining position stateAt) ->
  (forall stateAt,
    nth_error states 409 = Some stateAt ->
    writeSuccessWithdrawalsTerminalPositionState remaining stateAt) ->
  (forall stateAt,
    nth_error states 410 = Some stateAt ->
    writeSuccessWithdrawalsConcretePc stateAt =
      Some (if remaining is O then 0x156e8 else 0x15694) /\
    stateAt.1.1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat remaining)))) ->
  WriteSuccessWithdrawalsIndexedRun remaining before segments states.
Proof.
  intros Hlength Hstart Hedges HpositionState HterminalState HfinalState.
  split; first exact Hlength.
  split; first exact Hstart.
  intros position Hposition.
  destruct (Hedges position Hposition) as
    (observations & beforeAt & afterAt & Hobservations & Hbefore & Hafter &
     Hrun).
  exists observations, beforeAt, afterAt.
  split; first exact Hobservations.
  split; first exact Hbefore.
  split; first exact Hafter.
  split; first exact Hrun.
  destruct (Nat.lt_ge_cases position 408) as [Hordinary|Hspecial].
  - left. split; first exact Hordinary.
    split.
    + eapply HpositionState; [lia|exact Hbefore].
    + eapply HpositionState; [lia|exact Hafter].
  - destruct (Nat.eq_dec position 408%nat) as [->|Hnot408].
    + right. left. split; first reflexivity.
      split.
      * eapply HpositionState; [lia|exact Hbefore].
      * eapply HterminalState. exact Hafter.
    + have Hposition409 : position = 409%nat by lia. subst position.
      right. right. split; first reflexivity.
      split.
      * eapply HterminalState. exact Hbefore.
      * destruct (HfinalState afterAt Hafter) as (Hpc & Hx9).
        split; assumption.
Qed.

Print Assumptions writeSuccessWithdrawalsIndexedRunFromStateEquations.
