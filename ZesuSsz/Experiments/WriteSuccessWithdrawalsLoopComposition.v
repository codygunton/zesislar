From Coq Require Import Lia Lists.List.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.

Lemma writeSuccessWithdrawalsRecordedRunIterationCons n before firstSegments
    middle restSegments after :
  WriteSuccessWithdrawalsRecordedRun 410 before firstSegments middle ->
  WriteSuccessWithdrawalsRecordedRun (410 * n) middle restSegments after ->
  WriteSuccessWithdrawalsRecordedRun (410 * S n) before
    (firstSegments ++ restSegments) after.
Proof.
  intros Hfirst Hrest.
  replace (410 * S n)%nat with (410 + 410 * n)%nat by lia.
  eapply writeSuccessWithdrawalsRecordedRunApp; eassumption.
Qed.

Lemma writeSuccessWithdrawalsIterationLogCons
    (priorLog firstRecords middleLog restRecords finalLog :
      list WriteSuccessWithdrawalsRecord) :
  middleLog = priorLog ++ firstRecords ->
  finalLog = middleLog ++ restRecords ->
  finalLog = priorLog ++ (firstRecords ++ restRecords).
Proof. intros -> ->. symmetry. apply app_assoc. Qed.

Print Assumptions writeSuccessWithdrawalsRecordedRunIterationCons.
Print Assumptions writeSuccessWithdrawalsIterationLogCons.
