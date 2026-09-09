From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4EncoderIntRecorded.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.

Lemma writeSuccessWithdrawals156b4SecondEncoderRecorded args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs global :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
    withdrawal = writeSuccess15d10Before regs global ->
  exists segments,
    WriteSuccessWithdrawalsRecordedRun 3
      (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal,
       priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
         (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal))
      segments
      (writeSuccessWithdrawalsSecondEncoderEntry regs global sp withdrawal,
       priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
         (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)).
Proof.
  intros Hinv Hprefix Hentry.
  destruct (writeSuccessWithdrawalsFirstEncoderEndpointDirectFacts args sp
    pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs global Hinv Hprefix Hentry) as
    (mstatusBits & satp & oldDest & oldX1 & Hpc & Hsp & Hmstatus & Hsatp &
      Hdest & Hx1 & Hsys & HmstatusEval & Haligned & Hlower & Hupper & Hread &
      Htable).
  have HfirstInv := writeSuccessWithdrawals156a8EncoderIntInv args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    Hinv Hprefix.
  rewrite Hentry in HfirstInv.
  have Htable0 : writeSuccessWithdrawalsInstructionTable global by
    (unfold Inv_encoder_int in HfirstInv; cbn in HfirstInv; tauto).
  rewrite (writeSuccessWithdrawalsFirstEncoderEndpointBefore regs global sp
    withdrawal Htable0).
  unfold writeSuccessWithdrawalsSecondEncoderEntry.
  eapply writeSuccessWithdrawals156b4EncoderIntRecordedDirect; eassumption.
Qed.

Print Assumptions writeSuccessWithdrawals156b4SecondEncoderRecorded.
