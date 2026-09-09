From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationOff.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntFrame.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntCallerFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputEndpointFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.

Lemma writeSuccessWithdrawals156c0OutputInv args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer = writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current withdrawal = writeSuccess15d10Before regs1 global1 ->
  writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal = writeSuccess15d10Before regs2 global2 ->
  Inv_write_output (sp + BV 64 1768)%bv (BV 64 20) (Z_to_bv 64 0x156d0)
    (writeSuccessWithdrawalAddressBytes withdrawal)
    (writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp withdrawal)
    (writeSuccessWithdrawalsOutputEntry
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs)
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).2
      (sp + BV 64 1768)%bv,
     writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp withdrawal).
Proof.
  intros Hinv Hprefix Hentry1 Hentry2.
  destruct (writeSuccessWithdrawalsSecondEncoderEndpointDirectFacts args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 Hinv Hprefix Hentry1 Hentry2) as (x11 & x10 & x1 & Hpc & Hx11 & Hx18 & Hx10 & Hx1 & Hm & HtableEnd).
  have HfactsEnd := writeSuccessWithdrawalsSecondEncoderEndpointOperationalFacts args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 Hinv Hprefix Hentry1 Hentry2.
  have Hread := writeSuccessWithdrawalsSecondEncoderEndpointAddressRead args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 Hinv Hprefix Hentry1 Hentry2.
  have Hrepresentation : writeSuccessConcreteRepresentationOff (successStackPointer WriteSuccessObservation args) (successDecoded WriteSuccessObservation args) state.1.2.(seq_mem) (successDecodedAddress WriteSuccessObservation args) by (unfold Inv_15694 in Hinv; tauto).
  have Hnth : nth_error (observationWithdrawals (successDecoded WriteSuccessObservation args)) processed = Some withdrawal by (unfold Inv_15694 in Hinv; tauto).
  have Hvalid := proj1 (writeSuccessRepresentationWithdrawalAt _ _ _ _ _ _ Hrepresentation Hnth).
  have Hlength := writeSuccessWithdrawalAddressBytesLength withdrawal Hvalid.
  have Hinv2 := writeSuccessWithdrawals156b4SecondEncoderInv args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 Hinv Hprefix Hentry1.
  rewrite Hentry2 in Hinv2.
  have Htable2 : writeSuccessWithdrawalsInstructionTable global2 by (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  have Hrange : islaMemoryRange (bv_unsigned sp - 16) 16 by (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  have Hbacked : forall location, bv_unsigned sp - 16 <= location < bv_unsigned sp -> is_Some (global2.(seq_mem) !! Z_to_bv 64 location) by (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  have Hmmio2 : set_Forall (fun address => ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z) (dom global2.(seq_mem)) by (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  destruct (writeSuccessEncoderIntCaller156c0 global2 Htable2) as (Halign & trace & Hcode).
  have HendGlobal := writeSuccessWithdrawalsEncoderIntEndpointGlobal regs2 global2 sp (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal) trace Halign Hcode.
  have Hframe := writeSuccessEncoderIntGlobal2Frame global2 global2.(seq_mem) sp (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal) Hrange Hbacked ltac:(split; [reflexivity|intros; reflexivity]).
  have HmmioEnd : set_Forall (fun address => ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z) (dom (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).2.(seq_mem)).
  { unfold writeSuccessWithdrawalsSecondEncoderEndpoint. rewrite HendGlobal.
    rewrite (proj1 Hframe). exact Hmmio2. }
  apply writeSuccessWithdrawalsOutputEntryInv; assumption.
Qed.

Print Assumptions writeSuccessWithdrawals156c0OutputInv.
