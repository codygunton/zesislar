From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15698.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1569c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156ac.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156bc.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntCallerFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.

Lemma writeSuccessWithdrawalsPrefixAfterX18 state sp pointer :
  state.1.(seq_regs) !! "x18" = Some (RVal_Bits (sp + BV 64 1768)%bv) ->
  (writeSuccessWithdrawalsPrefixAfter state sp pointer).1.(seq_regs) !! "x18" =
    Some (RVal_Bits (sp + BV 64 1768)%bv).
Proof.
  intros Hx18. unfold writeSuccessWithdrawalsPrefixAfter,
    writeSuccessWithdrawalsPrefixStatea4, writeSuccessWithdrawalsPrefixStatea0,
    writeSuccessWithdrawalsPrefixState9c, writeSuccessWithdrawalsPrefixState98.
  unfold writeSuccess156a4After, writeSuccess156a0After,
    writeSuccess1569cAfter, writeSuccess15698After, writeSuccess15694After,
    writeSuccess15694Local. cbn.
  rewrite writeSuccess156a4RegsLookupOther; try discriminate.
  rewrite writeSuccess156a0RegsLookupOther; try discriminate.
  rewrite writeSuccess1569cRegsLookupOther; try discriminate.
  rewrite writeSuccess15698RegsLookupOther; try discriminate.
  rewrite writeSuccess15694RegsLookupOther; try discriminate.
  exact Hx18.
Qed.

Lemma writeSuccessWithdrawalsSecondEncoderEndpointX18 args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
    withdrawal = writeSuccess15d10Before regs1 global1 ->
  writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal =
    writeSuccess15d10Before regs2 global2 ->
  (writeSuccessWithdrawalsEncoderIntEndpoint regs2 global2 sp
    (Z_to_bv 64 0x156c0)
    (writeSuccessWithdrawalsValidatorValue withdrawal)).1.(seq_regs) !! "x18" =
    Some (RVal_Bits (sp + BV 64 1768)%bv).
Proof.
  intros Hinv Hprefix Hentry1 Hentry2.
  have Hx18 : state.1.1.(seq_regs) !! "x18" =
      Some (RVal_Bits (sp + BV 64 1768)%bv) by
    (unfold Inv_15694 in Hinv; tauto).
  have HprefixX18 := writeSuccessWithdrawalsPrefixAfterX18 state.1 sp pointer Hx18.
  have Hregs0 : regs0 !! "x18" = Some (RVal_Bits (sp + BV 64 1768)%bv).
  { pose proof (f_equal (fun machine => machine.1.(seq_regs)) Hprefix) as H.
    cbn in H. rewrite <- H. exact HprefixX18. }
  have Hregs1 : regs1 !! "x18" = Some (RVal_Bits (sp + BV 64 1768)%bv).
  { pose proof (f_equal (fun machine => machine.1.(seq_regs)) Hentry1) as H.
    cbn in H. rewrite <- H.
    unfold writeSuccessWithdrawalsEncoderInt156b4State,
      writeSuccess156b0After, writeSuccess156acAfter, writeSuccess156a8After,
      writeSuccess15694Local. cbn.
    rewrite writeSuccess156b0RegsLookupOther; try discriminate.
    rewrite writeSuccess156acRegsLookupOther; try discriminate.
    rewrite writeSuccess156a8RegsLookupOther; try discriminate.
    unfold writeSuccessWithdrawals156a8Regs.
    rewrite writeSuccessMemcpyEndpointLookupOther; try discriminate.
    exact Hregs0. }
  have HfirstInv := writeSuccessWithdrawals156a8EncoderIntInv args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 Hinv Hprefix.
  rewrite Hentry1 in HfirstInv.
  have Htable1 : writeSuccessWithdrawalsInstructionTable global1 by
    (unfold Inv_encoder_int in HfirstInv; cbn in HfirstInv; tauto).
  destruct (writeSuccessEncoderIntCaller156b4 global1 Htable1) as
    (Halign1 & trace1 & Hcode1).
  have HfirstX18 := writeSuccessWithdrawalsEncoderIntEndpointLookupOther regs1
    global1 sp (Z_to_bv 64 0x156b4)
    (writeSuccessWithdrawalsIndexValue withdrawal) trace1 "x18" Halign1 Hcode1
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate).
  rewrite Hregs1 in HfirstX18.
  have Hregs2 : regs2 !! "x18" = Some (RVal_Bits (sp + BV 64 1768)%bv).
  { pose proof (f_equal (fun machine => machine.1.(seq_regs)) Hentry2) as H.
    cbn in H. rewrite <- H.
    unfold writeSuccessWithdrawalsSecondEncoderEntry, writeSuccess156bcAfter,
      writeSuccess15694Local. cbn.
    rewrite writeSuccess156bcRegsLookupOther; try discriminate.
    rewrite writeSuccess156b8RegsLookupOther; try discriminate.
    rewrite writeSuccess156b4RegsLookupOther; try discriminate.
    exact HfirstX18. }
  have Hinv2 := writeSuccessWithdrawals156b4SecondEncoderInv args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    regs1 global1 Hinv Hprefix Hentry1.
  rewrite Hentry2 in Hinv2.
  have Htable2 : writeSuccessWithdrawalsInstructionTable global2 by
    (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  destruct (writeSuccessEncoderIntCaller156c0 global2 Htable2) as
    (Halign2 & trace2 & Hcode2).
  rewrite (writeSuccessWithdrawalsEncoderIntEndpointLookupOther regs2 global2 sp
    (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal)
    trace2 "x18" Halign2 Hcode2); try discriminate.
  exact Hregs2.
Qed.

Print Assumptions writeSuccessWithdrawalsPrefixAfterX18.
Print Assumptions writeSuccessWithdrawalsSecondEncoderEndpointX18.
