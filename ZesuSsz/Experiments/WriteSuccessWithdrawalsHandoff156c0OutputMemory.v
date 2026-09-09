From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntCallerFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalAddressRead.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.

Lemma writeSuccessWithdrawalsSecondEncoderEndpointAddressRead args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer = writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current withdrawal = writeSuccess15d10Before regs1 global1 ->
  writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal = writeSuccess15d10Before regs2 global2 ->
  read_mem_list (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).2.(seq_mem)
    (bv_unsigned (sp + BV 64 1768)%bv) 20 =
    Some (writeSuccessWithdrawalAddressBytes withdrawal).
Proof.
  intros Hinv Hprefix Hentry1 Hentry2.
  have Hread := writeSuccessWithdrawalsFinalAddressRead args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 (writeSuccessWithdrawalsIndexValue withdrawal) (writeSuccessWithdrawalsValidatorValue withdrawal) Hinv.
  have Hinv1 := writeSuccessWithdrawals156a8EncoderIntInv args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 Hinv Hprefix.
  rewrite Hentry1 in Hinv1.
  have Htable1 : writeSuccessWithdrawalsInstructionTable global1 by (unfold Inv_encoder_int in Hinv1; cbn in Hinv1; tauto).
  destruct (writeSuccessEncoderIntCaller156b4 global1 Htable1) as (Halign1 & trace1 & Hcode1).
  have Hend1 := writeSuccessWithdrawalsEncoderIntEndpointGlobal regs1 global1 sp (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal) trace1 Halign1 Hcode1.
  have Hinv2 := writeSuccessWithdrawals156b4SecondEncoderInv args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 Hinv Hprefix Hentry1.
  rewrite Hentry2 in Hinv2.
  have Htable2 : writeSuccessWithdrawalsInstructionTable global2 by (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  destruct (writeSuccessEncoderIntCaller156c0 global2 Htable2) as (Halign2 & trace2 & Hcode2).
  have Hend2 := writeSuccessWithdrawalsEncoderIntEndpointGlobal regs2 global2 sp (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal) trace2 Halign2 Hcode2.
  have Hg1 := f_equal snd Hentry1. cbn in Hg1.
  have Hg2 := f_equal snd Hentry2. cbn in Hg2.
  unfold writeSuccessWithdrawalsSecondEncoderEndpoint. rewrite Hend2.
  rewrite <- Hg2, Hend1, <- Hg1. exact Hread.
Qed.

Print Assumptions writeSuccessWithdrawalsSecondEncoderEndpointAddressRead.
