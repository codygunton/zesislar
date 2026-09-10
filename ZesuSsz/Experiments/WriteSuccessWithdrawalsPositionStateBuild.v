From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankIndexed.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.

Lemma writeSuccessWithdrawalsPositionStateBuild remaining position state pc :
  (position < 409)%nat ->
  nth_error writeSuccessWithdrawalsIterationPcs position = Some pc ->
  writeSuccessWithdrawalsConcretePc state = Some pc ->
  writeSuccessWithdrawalsSelectedOccurrence state pc =
    Some (count_occ Z.eq_dec
      (firstn position writeSuccessWithdrawalsIterationPcs) pc) ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  writeSuccessWithdrawalsPositionState remaining position state.
Proof.
  intros Hposition Hnth Hpc Hocc Hx9 Hrange. exists pc.
  destruct (writeSuccessWithdrawalsOrdinaryPosition position pc Hposition Hnth)
    as (HnotE4 & HnotE8 & Hnot8c & Hnot90).
  repeat split; assumption.
Qed.

Print Assumptions writeSuccessWithdrawalsPositionStateBuild.
