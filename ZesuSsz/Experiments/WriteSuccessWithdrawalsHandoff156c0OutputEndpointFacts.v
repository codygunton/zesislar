From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntCallerFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointPreservation.

Lemma writeSuccessWithdrawalsSecondEncoderEndpointOperationalFacts args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer = writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current withdrawal = writeSuccess15d10Before regs1 global1 ->
  writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal = writeSuccess15d10Before regs2 global2 ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs).
Proof.
  intros Hinv Hprefix Hentry1 Hentry2.
  have Hinv2 := writeSuccessWithdrawals156b4SecondEncoderInv args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 Hinv Hprefix Hentry1.
  rewrite Hentry2 in Hinv2.
  have Hfacts : writeSuccessWithdrawalsOperationalRegisterFacts regs2 by (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  have Hend := writeSuccessEncoderIntEndpointFacts regs2 sp (Z_to_bv 64 0x156c0) Hfacts.
  have Htable : writeSuccessWithdrawalsInstructionTable global2 by (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  destruct (writeSuccessEncoderIntCaller156c0 global2 Htable) as (Halign & trace & Hcode).
  have Hexact := writeSuccessEncoderIntEndpointExact regs2 global2 sp (writeSuccessWithdrawalsValidatorValue withdrawal) (Z_to_bv 64 0x156c0) trace Halign ltac:(rewrite writeSuccessWithdrawalsEncoderIntGlobal2Instrs; exact Hcode).
  unfold writeSuccessWithdrawalsSecondEncoderEndpoint, writeSuccessWithdrawalsEncoderIntEndpoint.
  rewrite Hexact. exact Hend.
Qed.

Print Assumptions writeSuccessWithdrawalsSecondEncoderEndpointOperationalFacts.
