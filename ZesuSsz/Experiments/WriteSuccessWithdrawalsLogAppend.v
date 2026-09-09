From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.

Import ListNotations.

Lemma writeSuccessWithdrawalsRecordedPayloads_agree log :
  writeSuccessWithdrawalsRecordedPayloads log = writeSuccessRecordedPayloads log.
Proof.
  destruct log; reflexivity.
Qed.

Lemma writeSuccessWithdrawalsRecordedPayloads_app
    first second firstPayloads secondPayloads :
  writeSuccessWithdrawalsRecordedPayloads first = Some firstPayloads ->
  writeSuccessWithdrawalsRecordedPayloads second = Some secondPayloads ->
  writeSuccessWithdrawalsRecordedPayloads (first ++ second) =
    Some (firstPayloads ++ secondPayloads).
Proof.
  intros Hfirst Hsecond.
  rewrite !writeSuccessWithdrawalsRecordedPayloads_agree in Hfirst, Hsecond |-.
  exact (writeSuccessRecordedPayloads_app first second firstPayloads
    secondPayloads Hfirst Hsecond).
Qed.

Lemma writeSuccessWithdrawalIterationRecords_append_payloads
    prior priorPayloads sp withdrawal records :
  writeSuccessWithdrawalsRecordedPayloads prior = Some priorPayloads ->
  writeSuccessWithdrawalIterationRecords sp withdrawal records ->
  writeSuccessWithdrawalsRecordedPayloads (prior ++ records) =
    Some (priorPayloads ++ writeSuccessWithdrawalFragments withdrawal).
Proof.
  intros Hprior [_ Hrecords].
  eapply writeSuccessWithdrawalsRecordedPayloads_app; eassumption.
Qed.

Print Assumptions writeSuccessWithdrawalsRecordedPayloads_agree.
Print Assumptions writeSuccessWithdrawalsRecordedPayloads_app.
Print Assumptions writeSuccessWithdrawalIterationRecords_append_payloads.
