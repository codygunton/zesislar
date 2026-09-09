From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1569c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694First.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Last.

Import ListNotations.

Lemma writeSuccessWithdrawalsPrefix15694Recorded args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  exists segments,
    WriteSuccessWithdrawalsRecordedRun 5 state segments
      (writeSuccessWithdrawalsPrefixAfter (fst state) sp pointer, priorLog).
Proof.
  intros Hinv.
  destruct (writeSuccessWithdrawalsPrefix15694FirstRecorded args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state Hinv) as
    (first & oldX1 & Hfirst & Hx1 & Htable & Hmstatus).
  set (middle := writeSuccessWithdrawalsPrefixStatea0 (fst state) sp pointer).
  have Hbefore : middle = writeSuccess156a0Before middle.1.(seq_regs) (snd middle).
  { unfold middle, writeSuccessWithdrawalsPrefixStatea0,
      writeSuccess1569cAfter. reflexivity. }
  have Hpca0 : middle.1.(seq_regs) !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x156a0)).
  { unfold middle, writeSuccessWithdrawalsPrefixStatea0,
      writeSuccess1569cAfter, writeSuccess1569cLocal,
      writeSuccess1569cRegs. cbn.
    rewrite lookup_insert writeSuccess1569cNextPcExact. reflexivity. }
  destruct (writeSuccessWithdrawalsPrefix15694LastRecorded middle priorLog oldX1
    Hbefore Hpca0 Hx1 Htable Hmstatus) as (last & Hlast).
  exists (first ++ last).
  change (WriteSuccessWithdrawalsRecordedRun (3 + 2) state (first ++ last)
    (writeSuccessWithdrawalsPrefixAfter (fst state) sp pointer, priorLog)).
  eapply writeSuccessWithdrawalsRecordedRunApp; first exact Hfirst.
  change (WriteSuccessWithdrawalsRecordedRun 2 (middle, priorLog) last
    (writeSuccessWithdrawalsPrefixLastAfter middle, priorLog)) in Hlast.
  exact Hlast.
Qed.

Print Assumptions writeSuccessWithdrawalsPrefix15694Recorded.
