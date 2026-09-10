From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8PositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationBounds.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankIndexed.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionStateBuild.

Open Scope Z_scope.

Lemma writeSuccessWithdrawals156b4HandoffPositionStates args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs
    global :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
    withdrawal = writeSuccess15d10Before regs global ->
  let first := writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp
    withdrawal in
  let second := writeSuccess156b4After first.1.(seq_regs) first.2
    (writeSuccessWithdrawalsValidatorValue withdrawal) in
  let third := writeSuccess156b8After second.1.(seq_regs) second.2 in
  writeSuccessWithdrawalsPositionState remaining 362 (first, priorLog) /\
  writeSuccessWithdrawalsPositionState remaining 363 (second, priorLog) /\
  writeSuccessWithdrawalsPositionState remaining 364 (third, priorLog).
Proof.
  intros Hinv Hprefix Hentry first second third.
  have Hrange : (Z.of_nat (S remaining) < 2 ^ 64)%Z.
  { have H := writeSuccessWithdrawalsIterationRemainingRange args sp pointer
      base total processed (S remaining) withdrawal allBytes prefix current
      suffix scratch encoderScratch registerFrame memoryFrame priorLog state Hinv.
    lia. }
  destruct (writeSuccessWithdrawals156a8HandoffPositionStates args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    Hinv Hprefix) as (_ & _ & Hb0).
  unfold writeSuccessWithdrawalsPositionState in Hb0.
  destruct Hb0 as (? & _ & _ & _ & Hx9b0 & _).
  have HentryRegs := f_equal (fun machine => machine.1.(seq_regs)) Hentry.
  cbn in HentryRegs.
  have Hx9regs : regs !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { rewrite <- HentryRegs.
    unfold writeSuccessWithdrawalsEncoderInt156b4State,
      writeSuccess156b0After, writeSuccess15694Local. cbn.
    rewrite writeSuccess156b0RegsLookupOther; try discriminate. exact Hx9b0. }
  have HfirstInv := writeSuccessWithdrawals156a8EncoderIntInv args sp pointer
    base total processed (S remaining) withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    Hinv Hprefix.
  rewrite Hentry in HfirstInv.
  have Halign : bv_extract 0 2 (Z_to_bv 64 0x156b4) = BV 2 0 by
    (unfold Inv_encoder_int in HfirstInv; cbn in HfirstInv; tauto).
  have Hcode : exists trace,
      global.(seq_instrs) !! Z_to_bv 64 0x156b4 = Some trace by
    (unfold Inv_encoder_int in HfirstInv; cbn in HfirstInv; tauto).
  destruct Hcode as (trace & Hcode).
  have Htable : writeSuccessWithdrawalsInstructionTable global by
    (unfold Inv_encoder_int in HfirstInv; cbn in HfirstInv; tauto).
  have HfirstBefore := writeSuccessWithdrawalsFirstEncoderEndpointBefore regs
    global sp withdrawal Htable.
  have HfirstPcReg : first.1.(seq_pc_reg) = "PC".
  { unfold first. rewrite HfirstBefore. reflexivity. }
  have HfirstPc : first.1.(seq_regs) !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x156b4)).
  { unfold first, writeSuccessWithdrawalsFirstEncoderEndpoint.
    eapply writeSuccessWithdrawalsEncoderIntEndpointPc; eassumption. }
  have Hx9first : first.1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold first, writeSuccessWithdrawalsFirstEncoderEndpoint.
    rewrite (writeSuccessWithdrawalsEncoderIntEndpointLookupOther regs global
      sp (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)
      trace "x9" Halign Hcode); try discriminate. exact Hx9regs. }
  have Hx9second : second.1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold second, writeSuccess156b4After, writeSuccess15694Local. cbn.
    rewrite writeSuccess156b4RegsLookupOther; try discriminate. exact Hx9first. }
  have Hx9third : third.1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold third, writeSuccess156b8After, writeSuccess15694Local. cbn.
    rewrite writeSuccess156b8RegsLookupOther; try discriminate. exact Hx9second. }
  repeat split.
  - eapply (writeSuccessWithdrawalsPositionStateBuild remaining 362
      (first, priorLog) 0x156b4).
    + lia.
    + reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc. cbn. rewrite HfirstPcReg.
      rewrite HfirstPc. unfold bvn_unsigned. cbn. rewrite Z_to_bv_unsigned.
      vm_compute. reflexivity.
    + unfold writeSuccessWithdrawalsSelectedOccurrence. native_compute.
      reflexivity.
    + exact Hx9first.
    + exact Hrange.
  - eapply (writeSuccessWithdrawalsPositionStateBuild remaining 363
      (second, priorLog) 0x156b8).
    + lia.
    + reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc, second, writeSuccess156b4After,
        writeSuccess15694Local. cbn. rewrite lookup_insert.
      rewrite writeSuccess156b4NextPcExact.
      unfold bvn_unsigned. cbn. rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + unfold writeSuccessWithdrawalsSelectedOccurrence. native_compute.
      reflexivity.
    + exact Hx9second.
    + exact Hrange.
  - eapply (writeSuccessWithdrawalsPositionStateBuild remaining 364
      (third, priorLog) 0x156bc).
    + lia.
    + reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc, third, writeSuccess156b8After,
        writeSuccess15694Local. cbn. rewrite lookup_insert.
      rewrite writeSuccess156b8NextPcExact. unfold bvn_unsigned. cbn.
      rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + unfold writeSuccessWithdrawalsSelectedOccurrence. native_compute.
      reflexivity.
    + exact Hx9third.
    + exact Hrange.
Qed.

Print Assumptions writeSuccessWithdrawals156b4HandoffPositionStates.
