From Coq Require Import Lia ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156cc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c0.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInvContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0PositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationBounds.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsOutputPositionContext args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 outputRegs outputGlobal :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
    withdrawal = writeSuccess15d10Before regs1 global1 ->
  writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal =
    writeSuccess15d10Before regs2 global2 ->
  writeSuccessWithdrawalsOutputEntry
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
        withdrawal).1.(seq_regs)
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
        withdrawal).2
      (sp + BV 64 1768)%bv = writeSuccess10190Before outputRegs outputGlobal ->
  outputRegs !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156d0)) /\
  outputRegs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) /\
  (Z.of_nat (S remaining) < 2 ^ 64)%Z.
Proof.
  intros Hinv Hprefix Hentry1 Hentry2 Houtput.
  have Hrange : (Z.of_nat (S remaining) < 2 ^ 64)%Z.
  { have H := writeSuccessWithdrawalsIterationRemainingRange args sp pointer
      base total processed (S remaining) withdrawal allBytes prefix current
      suffix scratch encoderScratch registerFrame memoryFrame priorLog state Hinv.
    lia. }
  have HoutputInv := writeSuccessWithdrawals156c0OutputInv args sp pointer base
    total processed (S remaining) withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    regs1 global1 regs2 global2 Hinv Hprefix Hentry1 Hentry2.
  rewrite Houtput in HoutputInv.
  have Hx1 : outputRegs !! "x1" =
      Some (RVal_Bits (Z_to_bv 64 0x156d0)) by
    (unfold Inv_write_output in HoutputInv; cbn in HoutputInv; tauto).
  have Hstates := writeSuccessWithdrawals156c0HandoffPositionStates args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    regs1 global1 regs2 global2 Hinv Hprefix Hentry1 Hentry2.
  specialize (Hstates 3%nat
    (writeSuccess156c8After
      (writeSuccess156c4Regs
        (writeSuccess156c0Regs
          (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
            withdrawal).1.(seq_regs))
        (sp + BV 64 1768)%bv)
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
        withdrawal).2,
     priorLog) ltac:(lia) eq_refl).
  unfold writeSuccessWithdrawalsPositionState in Hstates.
  destruct Hstates as (? & _ & _ & _ & Hx9before & _).
  have HoutputRegs := f_equal (fun machine => machine.1.(seq_regs)) Houtput.
  cbn in HoutputRegs.
  have Hx9 : outputRegs !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { rewrite <- HoutputRegs.
    unfold writeSuccessWithdrawalsOutputEntry, writeSuccess156ccAfter,
      writeSuccess15694Local. cbn.
    rewrite writeSuccess156ccRegsLookupOther; try discriminate.
    exact Hx9before. }
  repeat split; assumption.
Qed.

Print Assumptions writeSuccessWithdrawalsOutputPositionContext.
