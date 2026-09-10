From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15698.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1569c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156ac.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationBounds.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpy.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpySupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankIndexed.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionStateBuild.

Open Scope Z_scope.

Lemma writeSuccessWithdrawals156a8HandoffPositionStates args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs global :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs global ->
  writeSuccessWithdrawalsPositionState remaining 344
    (writeSuccessWithdrawals156a8State regs global sp pointer current, priorLog) /\
  writeSuccessWithdrawalsPositionState remaining 345
    (writeSuccessWithdrawals156acState regs global sp pointer current withdrawal,
     priorLog) /\
  writeSuccessWithdrawalsPositionState remaining 346
    (writeSuccessWithdrawals156b0State regs global sp pointer current withdrawal,
     priorLog).
Proof.
  intros Hinv Hentry.
  have Hrange : (Z.of_nat (S remaining) < 2 ^ 64)%Z.
  { have H := writeSuccessWithdrawalsIterationRemainingRange args sp pointer
      base total processed (S remaining) withdrawal allBytes prefix current
      suffix scratch encoderScratch registerFrame memoryFrame priorLog state Hinv.
    lia. }
  have Hx9 : regs !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { have HentryRegs := f_equal (fun machine => machine.1.(seq_regs)) Hentry.
    cbn in HentryRegs. rewrite <- HentryRegs.
    unfold writeSuccessWithdrawalsPrefixAfter,
      writeSuccessWithdrawalsPrefixStatea4,
      writeSuccessWithdrawalsPrefixStatea0,
      writeSuccessWithdrawalsPrefixState9c,
      writeSuccessWithdrawalsPrefixState98,
      writeSuccess156a4After, writeSuccess156a0After,
      writeSuccess1569cAfter, writeSuccess15698After,
      writeSuccess15694After, writeSuccess15694Local,
      writeSuccess1569cLocal. cbn.
    rewrite writeSuccess156a4RegsLookupOther; try discriminate.
    rewrite writeSuccess156a0RegsLookupOther; try discriminate.
    rewrite writeSuccess1569cRegsLookupOther; try discriminate.
    rewrite writeSuccess15698RegsLookupOther; try discriminate.
    rewrite writeSuccess15694RegsLookupOther; try discriminate.
    unfold Inv_15694 in Hinv. tauto. }
  have Hx9a8 : writeSuccessWithdrawals156a8Regs regs global sp pointer current
      !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold writeSuccessWithdrawals156a8Regs.
    rewrite writeSuccessMemcpyEndpointLookupOther; try discriminate. exact Hx9. }
  have Hx9ac :
      (writeSuccessWithdrawals156acState regs global sp pointer current
        withdrawal).1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold writeSuccessWithdrawals156acState, writeSuccess156a8After,
      writeSuccess15694Local. cbn. rewrite writeSuccess156a8RegsLookupOther;
      try discriminate. exact Hx9a8. }
  have Hx9b0 :
      (writeSuccessWithdrawals156b0State regs global sp pointer current
        withdrawal).1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold writeSuccessWithdrawals156b0State, writeSuccess156acAfter,
      writeSuccess15694Local. cbn. rewrite writeSuccess156acRegsLookupOther;
      try discriminate. exact Hx9ac. }
  repeat split.
  - eapply (writeSuccessWithdrawalsPositionStateBuild remaining 344
      (writeSuccessWithdrawals156a8State regs global sp pointer current,
       priorLog) 0x156a8).
    + lia.
    + reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc,
        writeSuccessWithdrawals156a8State. cbn.
      rewrite writeSuccessWithdrawals156a8RegsPc. unfold bvn_unsigned. cbn.
      rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + unfold writeSuccessWithdrawalsSelectedOccurrence. native_compute.
      reflexivity.
    + exact Hx9a8.
    + exact Hrange.
  - eapply (writeSuccessWithdrawalsPositionStateBuild remaining 345
      (writeSuccessWithdrawals156acState regs global sp pointer current
        withdrawal, priorLog) 0x156ac).
    + lia.
    + reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc. cbn.
      rewrite writeSuccessWithdrawals156acPc. unfold bvn_unsigned. cbn.
      rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + unfold writeSuccessWithdrawalsSelectedOccurrence. native_compute.
      reflexivity.
    + exact Hx9ac.
    + exact Hrange.
  - eapply (writeSuccessWithdrawalsPositionStateBuild remaining 346
      (writeSuccessWithdrawals156b0State regs global sp pointer current
        withdrawal, priorLog) 0x156b0).
    + lia.
    + reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc. cbn.
      rewrite writeSuccessWithdrawals156b0Pc. unfold bvn_unsigned. cbn.
      rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + unfold writeSuccessWithdrawalsSelectedOccurrence. native_compute.
      reflexivity.
    + exact Hx9b0.
    + exact Hrange.
Qed.

Print Assumptions writeSuccessWithdrawals156a8HandoffPositionStates.
