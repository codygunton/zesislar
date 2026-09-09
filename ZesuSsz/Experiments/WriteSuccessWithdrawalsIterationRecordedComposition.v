From Coq Require Import Lists.List.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Lemma writeSuccessWithdrawalsRecordedRunTenPhase
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10
    g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 :
  WriteSuccessWithdrawalsRecordedRun 344 s0 g0 s1 ->
  WriteSuccessWithdrawalsRecordedRun 3 s1 g1 s2 ->
  WriteSuccessWithdrawalsRecordedRun 15 s2 g2 s3 ->
  WriteSuccessWithdrawalsRecordedRun 3 s3 g3 s4 ->
  WriteSuccessWithdrawalsRecordedRun 15 s4 g4 s5 ->
  WriteSuccessWithdrawalsRecordedRun 4 s5 g5 s6 ->
  WriteSuccessWithdrawalsRecordedRun 5 s6 g6 s7 ->
  WriteSuccessWithdrawalsRecordedRun 3 s7 g7 s8 ->
  WriteSuccessWithdrawalsRecordedRun 15 s8 g8 s9 ->
  WriteSuccessWithdrawalsRecordedRun 3 s9 g9 s10 ->
  WriteSuccessWithdrawalsRecordedRun 410 s0
    (((((((((g0 ++ g1) ++ g2) ++ g3) ++ g4) ++ g5) ++ g6) ++ g7) ++ g8) ++ g9)
    s10.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
  assert (H01 : WriteSuccessWithdrawalsRecordedRun 347 s0 (g0 ++ g1) s2).
  { replace 347%nat with (344 + 3)%nat by reflexivity.
    eapply writeSuccessWithdrawalsRecordedRunApp; eassumption. }
  assert (H012 : WriteSuccessWithdrawalsRecordedRun 362 s0
      ((g0 ++ g1) ++ g2) s3).
  { replace 362%nat with (347 + 15)%nat by reflexivity.
    eapply writeSuccessWithdrawalsRecordedRunApp; eassumption. }
  assert (H0123 : WriteSuccessWithdrawalsRecordedRun 365 s0
      (((g0 ++ g1) ++ g2) ++ g3) s4).
  { replace 365%nat with (362 + 3)%nat by reflexivity.
    eapply writeSuccessWithdrawalsRecordedRunApp; eassumption. }
  assert (H01234 : WriteSuccessWithdrawalsRecordedRun 380 s0
      ((((g0 ++ g1) ++ g2) ++ g3) ++ g4) s5).
  { replace 380%nat with (365 + 15)%nat by reflexivity.
    eapply writeSuccessWithdrawalsRecordedRunApp; eassumption. }
  assert (H012345 : WriteSuccessWithdrawalsRecordedRun 384 s0
      (((((g0 ++ g1) ++ g2) ++ g3) ++ g4) ++ g5) s6).
  { replace 384%nat with (380 + 4)%nat by reflexivity.
    eapply writeSuccessWithdrawalsRecordedRunApp; eassumption. }
  assert (H0123456 : WriteSuccessWithdrawalsRecordedRun 389 s0
      ((((((g0 ++ g1) ++ g2) ++ g3) ++ g4) ++ g5) ++ g6) s7).
  { replace 389%nat with (384 + 5)%nat by reflexivity.
    eapply writeSuccessWithdrawalsRecordedRunApp; eassumption. }
  assert (H01234567 : WriteSuccessWithdrawalsRecordedRun 392 s0
      (((((((g0 ++ g1) ++ g2) ++ g3) ++ g4) ++ g5) ++ g6) ++ g7) s8).
  { replace 392%nat with (389 + 3)%nat by reflexivity.
    eapply writeSuccessWithdrawalsRecordedRunApp; eassumption. }
  assert (H012345678 : WriteSuccessWithdrawalsRecordedRun 407 s0
      ((((((((g0 ++ g1) ++ g2) ++ g3) ++ g4) ++ g5) ++ g6) ++ g7) ++ g8) s9).
  { replace 407%nat with (392 + 15)%nat by reflexivity.
    eapply writeSuccessWithdrawalsRecordedRunApp; eassumption. }
  replace 410%nat with (407 + 3)%nat by reflexivity.
  eapply writeSuccessWithdrawalsRecordedRunApp; eassumption.
Qed.

Print Assumptions writeSuccessWithdrawalsRecordedRunTenPhase.
