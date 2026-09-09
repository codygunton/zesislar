From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_94.a156d0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalAmountRead.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156d0EncoderIntContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156d0EncoderIntCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOutputCallerFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOutputEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Open Scope Z_scope.

Lemma writeSuccessWithdrawals156d0FinalEncoderCovered args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    outputRegs global outputPriorLog (firstValue secondValue : bv 64)
    segments after :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  global = writeSuccessEncoderIntGlobal2
    (writeSuccessEncoderIntGlobal2
      (writeSuccessWithdrawals156a8Global regs0 global0 sp pointer current) sp
      (Z_to_bv 64 0x156b4) firstValue) sp
    (Z_to_bv 64 0x156c0) secondValue ->
  outputRegs !! "x2" = Some (RVal_Bits sp) ->
  Inv_write_output (sp + BV 64 1768)%bv (BV 64 20)
    (Z_to_bv 64 0x156d0) (writeSuccessWithdrawalAddressBytes withdrawal)
    outputPriorLog (writeSuccess10190Before outputRegs global, outputPriorLog) ->
  WriteSuccessWithdrawalsRecordedRun 3
    (writeSuccess101a0After (writeSuccessOutputRegs4 outputRegs) global
       (Z_to_bv 64 0x156d0),
     outputPriorLog ++ writeSuccessWithdrawalsOutputRecordsExact global
       (sp + BV 64 1768)%bv (BV 64 20)) segments after ->
  after =
    (writeSuccess156d8After
      (writeSuccess156d4Regs
        (writeSuccess156d0Regs
          (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0))
          (writeSuccessWithdrawalsAmountValue withdrawal))) global,
     outputPriorLog ++ writeSuccessWithdrawalsOutputRecordsExact global
       (sp + BV 64 1768)%bv (BV 64 20)).
Proof.
  intros Hinv Hglobal Hx2 HoutputInv Hrun.
  have Htable : writeSuccessWithdrawalsInstructionTable global by
    (unfold Inv_write_output in HoutputInv; cbn in HoutputInv; tauto).
  destruct (writeSuccessOutputCaller156d0 global Htable) as
    (HreturnAlign & returnTrace & HreturnCode).
  have Hstart := writeSuccessOutputEndpointExact outputRegs global
    (Z_to_bv 64 0x156d0) returnTrace HreturnAlign HreturnCode.
  have Hcode : global.(seq_instrs) !! Z_to_bv 64 0x156d0 = Some a156d0 by
    (apply Htable; cbn; tauto).
  have Htrace : returnTrace = a156d0 by congruence.
  subst returnTrace.
  have Hfacts0 : writeSuccessWithdrawalsOperationalRegisterFacts outputRegs by
    (unfold Inv_write_output in HoutputInv; cbn in HoutputInv; tauto).
  have Hfacts := writeSuccessOutputEndpointFacts outputRegs
    (Z_to_bv 64 0x156d0) Hfacts0.
  have Hsp := writeSuccessWithdrawalsOutputEndpointX2 outputRegs sp Hx2.
  have HspAlign : bv_unsigned sp `mod` 16 = 0 by
    (unfold Inv_15694 in Hinv; tauto).
  have HspLower : 0x20000000 <= bv_unsigned sp - 16 by
    (unfold Inv_15694 in Hinv; tauto).
  have HspUpper : bv_unsigned sp + 1792 < 0x40000000 by
    (unfold Inv_15694 in Hinv; tauto).
  destruct (writeSuccessWithdrawals156d0Context
    (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0)) sp
    Hfacts Hsp HspAlign HspLower HspUpper) as
    (mstatusBits & satp & oldDest & oldX1 & Hmstatus & Hsatp & Hdest & Hx1 &
     Hsys & HmstatusEval & Haligned & Hlower & Hupper).
  have Hread := writeSuccessWithdrawalsFinalAmountRead args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    firstValue secondValue outputRegs Hinv.
  cbn -[writeSuccessEncoderIntGlobal2] in Hread.
  rewrite <- Hglobal in Hread.
  have HstartGlobal := f_equal snd Hstart.
  cbn in HstartGlobal. rewrite HstartGlobal in Hread.
  rewrite Hstart in Hrun.
  exact (writeSuccessWithdrawals156d0EncoderIntCoveredDirect
    (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0)) global sp
    (writeSuccessWithdrawalsAmountValue withdrawal)
    (outputPriorLog ++ writeSuccessWithdrawalsOutputRecordsExact global
      (sp + BV 64 1768)%bv (BV 64 20))
    mstatusBits satp oldDest oldX1 segments after
    ltac:(unfold writeSuccessOutputEndpointRegs, writeSuccess101a0Regs;
      rewrite lookup_insert;
      rewrite (writeSuccessOutputReturnTargetExact _ HreturnAlign); reflexivity)
    Hsp Hmstatus Hsatp Hdest Hx1 Hsys HmstatusEval Haligned Hlower Hupper
    Hread Htable Hrun).
Qed.

Print Assumptions writeSuccessWithdrawals156d0FinalEncoderCovered.
