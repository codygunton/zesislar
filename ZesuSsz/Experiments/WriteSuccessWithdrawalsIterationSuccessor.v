From Coq Require Import Lia Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.

Lemma writeSuccessWithdrawalsIterationSuccessor args sp pointer base total
    processed r withdrawal allBytes prefix current suffix scratch encoderScratch
    registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed (S (S r)) withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  exists nextWithdrawal nextCurrent nextSuffix,
    nth_error (observationWithdrawals
      (successDecoded WriteSuccessObservation args)) (S processed) =
      Some nextWithdrawal /\
    suffix = nextCurrent ++ nextSuffix /\
    length nextCurrent = 48%nat.
Proof.
  intros Hinv.
  have Htotal : total = length (observationWithdrawals
      (successDecoded WriteSuccessObservation args)) by
    (unfold Inv_15694 in Hinv; tauto).
  have Hremaining : total = (processed + S (S r))%nat by
    (unfold Inv_15694 in Hinv; tauto).
  have HsuffixLength : length suffix = (48 * S r)%nat by
    (unfold Inv_15694 in Hinv; cbn in Hinv; tauto).
  have Hindex : (S processed < length (observationWithdrawals
      (successDecoded WriteSuccessObservation args)))%nat by lia.
  destruct (nth_error (observationWithdrawals
      (successDecoded WriteSuccessObservation args)) (S processed)) as
    [nextWithdrawal|] eqn:Hnext.
  - exists nextWithdrawal, (firstn 48 suffix), (skipn 48 suffix).
    split; first reflexivity.
    split; first (symmetry; apply firstn_skipn).
    rewrite firstn_length HsuffixLength. lia.
  - exfalso.
    have Hsome := proj2 (nth_error_Some _ _) Hindex.
    rewrite Hnext in Hsome. contradiction.
Qed.

Print Assumptions writeSuccessWithdrawalsIterationSuccessor.
