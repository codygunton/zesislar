From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessBlockFramework.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsLoopItems.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsLoopRecords.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationSuccessor.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessWithdrawalsLoopFromBlocks remaining :
  block_15694_iteration_statement ->
  block_15694_last_iteration_statement ->
  forall args sp pointer base total processed withdrawal allBytes prefix current
      suffix scratch encoderScratch registerFrame memoryFrame priorLog state,
    remaining <> 0%nat ->
    Inv_15694 args sp pointer base total processed remaining withdrawal
      allBytes prefix current suffix scratch encoderScratch registerFrame
      memoryFrame priorLog state ->
    exists segments after records,
      IslaInstructionRun (410 * remaining) state.1 segments after.1 /\
      after.2 = priorLog ++ records /\
      writeSuccessWithdrawalLoopRecords sp
        (firstn remaining (skipn processed (observationWithdrawals
          (successDecoded WriteSuccessObservation args)))) records /\
      Inv_156e8 args sp (pointer + Z_to_bv 64 (48 * Z.of_nat remaining))%bv
        base total allBytes registerFrame memoryFrame (priorLog ++ records)
        after.
Proof.
  intros Hstep Hlast.
  induction remaining as [|remaining IH]; intros args sp pointer base total
    processed withdrawal allBytes prefix current suffix scratch encoderScratch
    registerFrame memoryFrame priorLog state Hpositive Hinv.
  { contradiction. }
  destruct remaining as [|r].
  - have HsuffixNil : suffix = [].
    { apply length_zero_iff_nil.
      have Hlength : length suffix = (48 * Nat.pred 1)%nat by
        (unfold Inv_15694 in Hinv; tauto).
      cbn in Hlength. exact Hlength. }
    subst suffix.
    unfold block_15694_last_iteration_statement in Hlast.
    destruct (Hlast args sp pointer base total processed withdrawal allBytes
      prefix current scratch encoderScratch registerFrame memoryFrame priorLog
      state ltac:(exact Hinv)) as
      (segments & after & records & padding & Hrun & Hlog & Hrecords & Hpadding &
       HcurrentShape & Hscratch & Hexit).
    exists segments, after, records.
    split.
    + cbn. exact Hrun.
    + split; first exact Hlog.
      split.
      * have Hnth : nth_error (observationWithdrawals
            (successDecoded WriteSuccessObservation args)) processed =
            Some withdrawal by (unfold Inv_15694 in Hinv; tauto).
        rewrite (writeSuccessWithdrawalsCurrentRemainingItems _ processed 0
          withdrawal Hnth).
        change (writeSuccessWithdrawalLoopRecords sp [withdrawal] records).
        exists [records]. split.
        -- constructor; first exact Hrecords. constructor.
        -- cbn. rewrite app_nil_r. reflexivity.
      * replace (pointer + Z_to_bv 64 (48 * Z.of_nat 1))%bv with
          (pointer + BV 64 48)%bv by
          (cbn; reflexivity).
        exact Hexit.
  - destruct (writeSuccessWithdrawalsIterationSuccessor args sp pointer base
      total processed r withdrawal allBytes prefix current suffix scratch
      encoderScratch registerFrame memoryFrame priorLog state Hinv) as
      (nextWithdrawal & nextCurrent & nextSuffix & Hnext & Hsuffix &
       HnextLength).
    unfold block_15694_iteration_statement in Hstep.
    rewrite Hsuffix in Hinv.
    destruct (Hstep args sp pointer base total processed r withdrawal
      nextWithdrawal allBytes prefix current nextCurrent nextSuffix scratch
      encoderScratch registerFrame memoryFrame priorLog state Hinv Hnext
      HnextLength) as
      (firstSegments & middle & firstRecords & padding & encoderAfter &
       HfirstRun & HmiddleLog & HfirstRecords & Hpadding & HcurrentShape &
       Hscratch & HnextInv).
    destruct (IH args sp (pointer + BV 64 48)%bv base total (S processed)
      nextWithdrawal allBytes (prefix ++ current) nextCurrent nextSuffix current
      encoderAfter registerFrame memoryFrame (priorLog ++ firstRecords) middle
      ltac:(discriminate) HnextInv) as
      (restSegments & after & restRecords & HrestRun & HafterLog & HrestRecords &
       Hexit).
    exists (firstSegments ++ restSegments), after,
      (firstRecords ++ restRecords).
    split.
    + replace (410 * S (S r))%nat with (410 + 410 * S r)%nat by lia.
      eapply islaInstructionRun_app; eassumption.
    + split.
      * rewrite HafterLog. symmetry. apply app_assoc.
      * split.
        -- have Hnth : nth_error (observationWithdrawals
              (successDecoded WriteSuccessObservation args)) processed =
              Some withdrawal by (unfold Inv_15694 in Hinv; tauto).
           rewrite (writeSuccessWithdrawalsCurrentRemainingItems _ processed
             (S r) withdrawal Hnth).
           apply writeSuccessWithdrawalLoopRecordsCons; assumption.
        -- replace
             (pointer + Z_to_bv 64 (48 * Z.of_nat (S (S r))))%bv with
             ((pointer + BV 64 48) +
               Z_to_bv 64 (48 * Z.of_nat (S r)))%bv.
           ++ rewrite app_assoc. exact Hexit.
           ++ bv_solve.
Qed.

Print Assumptions writeSuccessWithdrawalsLoopFromBlocks.
