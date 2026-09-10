From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_91.a156a8.
Require Import IslaTraces.write_success_91.a156ac.
Require Import IslaTraces.write_success_91.a156b0.
Require Import IslaTraces.write_success_07.a15d10.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156ac.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b0.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntPositionsFirst.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntPositionsSecond.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntPositionsLast.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Lemma writeSuccessWithdrawals156a8EncoderIntPositionsExact args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs global segments after :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer = writeSuccess101d4Before regs global ->
  WriteSuccessWithdrawalsRecordedRun 3
    (writeSuccessWithdrawals156a8State regs global sp pointer current, priorLog)
    segments after ->
  exists observations0 observations1 observations2,
    segments = [observations0; observations1; observations2] /\
    after = (writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer current withdrawal, priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccessWithdrawals156a8State regs global sp pointer current, priorLog)
      [observations0]
      (writeSuccessWithdrawals156acState regs global sp pointer current withdrawal, priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccessWithdrawals156acState regs global sp pointer current withdrawal, priorLog)
      [observations1]
      (writeSuccessWithdrawals156b0State regs global sp pointer current withdrawal, priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccessWithdrawals156b0State regs global sp pointer current withdrawal, priorLog)
      [observations2] after.
Proof.
  intros Hinv Hentry Hrecorded.
  destruct (writeSuccessWithdrawals156a8DirectFacts args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs global Hinv Hentry)
    as (mstatusBits & satp & oldDest & oldX1 & Hpc & Hsp & Hmstatus & Hsatp &
      Hdest & Hx1 & Hsys & Hma & Haligned & Hlower & Hupper & Hread & Htable).
  have Hcodea8 : (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_instrs)
      !! Z_to_bv 64 0x156a8 = Some a156a8.
  { rewrite writeSuccessWithdrawals156a8Instrs. apply Htable. cbn. tauto. }
  have Hcodeac : (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_instrs)
      !! Z_to_bv 64 0x156ac = Some a156ac.
  { rewrite writeSuccessWithdrawals156a8Instrs. apply Htable. cbn. tauto. }
  have Hcodeb0 : (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_instrs)
      !! Z_to_bv 64 0x156b0 = Some a156b0.
  { rewrite writeSuccessWithdrawals156a8Instrs. apply Htable. cbn. tauto. }
  have HcodeInt : (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_instrs)
      !! Z_to_bv 64 0x15d10 = Some a15d10.
  { rewrite writeSuccessWithdrawals156a8Instrs. apply Htable. cbn. tauto. }
  destruct Hrecorded as (Hrun & Hlog).
  destruct (writeSuccessWithdrawals156a8PositionsFirst regs global sp pointer current
    withdrawal mstatusBits satp oldDest segments after.1 Hpc Hsp Hmstatus Hsatp
    Hdest Hsys Hma Haligned Hlower Hupper Hread Hcodea8 Hcodeac Hrun) as
    (o0 & tail1 & Hsegments & Ho0 & Hrun2 & Hseg0).
  destruct (writeSuccessWithdrawals156a8PositionsSecond regs global sp pointer current
    withdrawal oldX1 tail1 after.1 Hx1 Hma Hcodeac Hcodeb0 Hrun2) as
    (o1 & tail2 & Htail1 & Ho1 & Hrun1 & Hseg1).
  destruct (writeSuccessWithdrawals156a8PositionsLast regs global sp pointer current
    withdrawal tail2 after.1 Hma Hcodeb0 HcodeInt Hrun1) as (Htail2 & Hmachine & Hseg2).
  destruct after as [afterMachine afterLog]. cbn in Hmachine, Hlog |- *.
  subst afterMachine.
  have Hsilent0 : concat (map microLabels o0) = [].
  { rewrite Ho0. unfold writeSuccess156a8Observations,
      writeSuccess156a8PrefixObservations, writeSuccess156a8ExecutionPrefix,
      writeSuccess156a8PreReadObservations, writeSuccess156a8PostReadPrefix.
    reflexivity. }
  have Hsilent1 : concat (map microLabels o1) = [].
  { rewrite Ho1. unfold writeSuccess156acObservations,
      writeSuccess156acPrefixObservations. reflexivity. }
  have Hsilent2 : concat (map microLabels
      (writeSuccess156b0Observations
        (writeSuccessWithdrawals156b0State regs global sp pointer current withdrawal).1.(seq_regs)
        (writeSuccessWithdrawals156b0State regs global sp pointer current withdrawal).2)) = [].
  { unfold writeSuccess156b0Observations, writeSuccess156b0PrefixObservations.
    reflexivity. }
  have HsegmentsAll : segments = [o0; o1;
      writeSuccess156b0Observations
        (writeSuccessWithdrawals156b0State regs global sp pointer current withdrawal).1.(seq_regs)
        (writeSuccessWithdrawals156b0State regs global sp pointer current withdrawal).2].
  { rewrite Hsegments Htail1 Htail2. reflexivity. }
  have Hlabels : concat (map microLabels (flattenMicroObservations segments)) = [].
  { rewrite HsegmentsAll. cbn [flattenMicroObservations].
    rewrite !map_app !concat_app Hsilent0 Hsilent1.
    exact Hsilent2. }
  rewrite (writeSuccessWithdrawalsSilentSegmentRecords _ _ Hlabels) in Hlog.
  rewrite app_nil_r in Hlog. subst afterLog.
  exists o0, o1,
    (writeSuccess156b0Observations
      (writeSuccessWithdrawals156b0State regs global sp pointer current withdrawal).1.(seq_regs)
      (writeSuccessWithdrawals156b0State regs global sp pointer current withdrawal).2).
  split; first exact HsegmentsAll.
  split; first reflexivity.
  split.
  - eapply (writeSuccessWithdrawalsSilentRecordedSnoc 0
      (writeSuccessWithdrawals156a8State regs global sp pointer current,
       priorLog) []
      (writeSuccessWithdrawals156a8State regs global sp pointer current,
       priorLog) o0
      (writeSuccessWithdrawals156acState regs global sp pointer current withdrawal)).
    + apply writeSuccessWithdrawalsRecordedRunZero.
    + exact Hseg0.
    + exact Hsilent0.
  - split.
    + eapply (writeSuccessWithdrawalsSilentRecordedSnoc 0
        (writeSuccessWithdrawals156acState regs global sp pointer current
          withdrawal, priorLog) []
        (writeSuccessWithdrawals156acState regs global sp pointer current
          withdrawal, priorLog) o1
        (writeSuccessWithdrawals156b0State regs global sp pointer current withdrawal)).
      * apply writeSuccessWithdrawalsRecordedRunZero.
      * exact Hseg1.
      * exact Hsilent1.
    + eapply (writeSuccessWithdrawalsSilentRecordedSnoc 0
        (writeSuccessWithdrawals156b0State regs global sp pointer current
          withdrawal, priorLog) []
        (writeSuccessWithdrawals156b0State regs global sp pointer current
          withdrawal, priorLog) _
        (writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer current withdrawal)).
      * apply writeSuccessWithdrawalsRecordedRunZero.
      * exact Hseg2.
      * exact Hsilent2.
Qed.

Print Assumptions writeSuccessWithdrawals156a8EncoderIntPositionsExact.
