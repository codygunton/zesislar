From Coq Require Import Lia ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156bc.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4PositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationBounds.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.

Open Scope Z_scope.

Lemma writeSuccessWithdrawals156c0PositionContext args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
    withdrawal = writeSuccess15d10Before regs1 global1 ->
  writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal =
    writeSuccess15d10Before regs2 global2 ->
  let endpoint := writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
    withdrawal in
  endpoint.1.(seq_pc_reg) = "PC" /\
  endpoint.1.(seq_regs) !! "PC" =
    Some (RVal_Bits (Z_to_bv 64 0x156c0)) /\
  endpoint.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) /\
  (Z.of_nat (S remaining) < 2 ^ 64)%Z.
Proof.
  intros Hinv Hprefix Hentry1 Hentry2 endpoint.
  have Hrange : (Z.of_nat (S remaining) < 2 ^ 64)%Z.
  { have H := writeSuccessWithdrawalsIterationRemainingRange args sp pointer
      base total processed (S remaining) withdrawal allBytes prefix current
      suffix scratch encoderScratch registerFrame memoryFrame priorLog state Hinv.
    lia. }
  destruct (writeSuccessWithdrawals156b4HandoffPositionStates args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    regs1 global1 Hinv Hprefix Hentry1) as (_ & _ & HthirdState).
  unfold writeSuccessWithdrawalsPositionState in HthirdState.
  destruct HthirdState as (? & _ & _ & _ & Hx9thirdEntry & _).
  have Hentry2Regs := f_equal (fun machine => machine.1.(seq_regs)) Hentry2.
  cbn in Hentry2Regs.
  have Hx9regs2 : regs2 !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { rewrite <- Hentry2Regs.
    unfold writeSuccessWithdrawalsSecondEncoderEntry,
      writeSuccess156bcAfter, writeSuccess15694Local. cbn.
    rewrite writeSuccess156bcRegsLookupOther; try discriminate.
    exact Hx9thirdEntry. }
  have Hinv2 := writeSuccessWithdrawals156b4SecondEncoderInv args sp pointer
    base total processed (S remaining) withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    regs1 global1 Hinv Hprefix Hentry1.
  rewrite Hentry2 in Hinv2.
  have Halign : bv_extract 0 2 (Z_to_bv 64 0x156c0) = BV 2 0 by
    (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  have Hcode : exists trace,
      global2.(seq_instrs) !! Z_to_bv 64 0x156c0 = Some trace by
    (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  destruct Hcode as (trace & Hcode).
  have Hx9 : endpoint.1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold endpoint, writeSuccessWithdrawalsSecondEncoderEndpoint.
    rewrite (writeSuccessWithdrawalsEncoderIntEndpointLookupOther regs2 global2
      sp (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal)
      trace "x9" Halign Hcode); try discriminate. exact Hx9regs2. }
  destruct (writeSuccessWithdrawalsSecondEncoderEndpointDirectFacts args sp
    pointer base total processed (S remaining) withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 regs2 global2 Hinv Hprefix Hentry1 Hentry2) as
    (? & ? & ? & Hpc & _).
  have Hbefore := writeSuccessWithdrawalsSecondEncoderEndpointBefore args sp
    pointer base total processed (S remaining) withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 regs2 global2 Hinv Hprefix Hentry1 Hentry2.
  have HpcReg : endpoint.1.(seq_pc_reg) = "PC".
  { unfold endpoint. rewrite Hbefore. reflexivity. }
  repeat split; assumption.
Qed.

Print Assumptions writeSuccessWithdrawals156c0PositionContext.
