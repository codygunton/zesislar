From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntRecorded.

Lemma writeSuccessWithdrawals156a8EncoderIntRecorded args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs global :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs global ->
  exists segments,
    WriteSuccessWithdrawalsRecordedRun 3
      (writeSuccessWithdrawals156a8State regs global sp pointer current, priorLog)
      segments
      (writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer current
        withdrawal, priorLog).
Proof.
  intros Hinv Hentry.
  destruct (writeSuccessWithdrawals156a8DirectFacts args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs global Hinv Hentry)
    as (mstatusBits & satp & oldDest & oldX1 & Hpc & Hsp & Hmstatus & Hsatp &
      Hdest & Hx1 & Hsys & HmstatusAssume & Haligned & Hlower & Hupper & Hread &
      Htable).
  eapply writeSuccessWithdrawals156a8EncoderIntRecordedDirect; eassumption.
Qed.

Print Assumptions writeSuccessWithdrawals156a8EncoderIntRecorded.
