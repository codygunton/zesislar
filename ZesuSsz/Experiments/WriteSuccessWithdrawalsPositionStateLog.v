Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankIndexed.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.

Lemma writeSuccessWithdrawalsPositionStateLog remaining position machine
    beforeLog afterLog :
  writeSuccessWithdrawalsPositionState remaining position (machine, beforeLog) ->
  writeSuccessWithdrawalsPositionState remaining position (machine, afterLog).
Proof.
  unfold writeSuccessWithdrawalsPositionState,
    writeSuccessWithdrawalsConcretePc,
    writeSuccessWithdrawalsSelectedOccurrence,
    writeSuccessWithdrawalsRegisterUnsigned.
  cbn. exact (fun H => H).
Qed.

Print Assumptions writeSuccessWithdrawalsPositionStateLog.
