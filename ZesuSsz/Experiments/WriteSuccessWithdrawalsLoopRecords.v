From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.

Import ListNotations.

Definition writeSuccessWithdrawalLoopRecords (sp : bv 64)
    (withdrawals : list WriteSuccessWithdrawalObservation)
    (records : list WriteSuccessWithdrawalsRecord) : Prop :=
  exists chunks,
    Forall2 (writeSuccessWithdrawalIterationRecords sp) withdrawals chunks /\
    records = concat chunks.

Lemma writeSuccessWithdrawalLoopRecordsNil sp :
  writeSuccessWithdrawalLoopRecords sp [] [].
Proof. exists []. split; constructor. Qed.

Lemma writeSuccessWithdrawalLoopRecordsCons sp withdrawal withdrawals records
    rest :
  writeSuccessWithdrawalIterationRecords sp withdrawal records ->
  writeSuccessWithdrawalLoopRecords sp withdrawals rest ->
  writeSuccessWithdrawalLoopRecords sp (withdrawal :: withdrawals)
    (records ++ rest).
Proof.
  intros Hrecords (chunks & Hchunks & Hrest).
  exists (records :: chunks). split.
  - constructor; assumption.
  - cbn. rewrite Hrest. reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawalLoopRecordsNil.
Print Assumptions writeSuccessWithdrawalLoopRecordsCons.
