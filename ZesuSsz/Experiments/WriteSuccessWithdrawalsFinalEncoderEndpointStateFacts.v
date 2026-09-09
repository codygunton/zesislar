From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
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
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156cc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntCallerFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntScratch.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalAddressRead.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalAmountRead.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalEncoderEndpointFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInvContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156d0FinalEncoderInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOutputEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpyState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRegisterUpdate.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalEncoderRegisterPreservation.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsFinalEncoderEndpointStateFacts args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 regs2 global2 outputRegs outputGlobal finalRegs
    finalGlobal :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
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
      withdrawal).2 (sp + BV 64 1768)%bv =
    writeSuccess10190Before outputRegs outputGlobal ->
  writeSuccess156d8After
      (writeSuccess156d4Regs
        (writeSuccess156d0Regs
          (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0))
          (writeSuccessWithdrawalsAmountValue withdrawal))) outputGlobal =
    writeSuccess15d10Before finalRegs finalGlobal ->
  let endpoint := writeSuccessWithdrawalsEncoderIntEndpoint finalRegs
    finalGlobal sp (Z_to_bv 64 0x156dc)
    (writeSuccessWithdrawalsAmountValue withdrawal) in
  endpoint.1.(seq_regs) !! "x2" = Some (RVal_Bits sp) /\
  writeSuccessWithdrawalsOperationalRegisterFacts endpoint.1.(seq_regs).
Proof.
  intros Hinv Hp He1 He2 Ho Hfinal. cbn.
  have Hpackage := writeSuccessWithdrawalsFinalEncoderEndpointPackage args sp
    pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 regs2 global2 outputRegs outputGlobal finalRegs
    finalGlobal Hinv Hp He1 He2 Ho Hfinal.
  cbn in Hpackage.
  destruct Hpackage as (_ & _ & _ & _ & _ & HtableEnd & _ & _ & HglobalEnd).
  have HoutputInv := writeSuccessWithdrawals156c0OutputInv args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 Hinv Hp He1 He2.
  rewrite Ho in HoutputInv.
  have Hinv2 := writeSuccessWithdrawals156b4SecondEncoderInv args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 Hinv Hp He1.
  rewrite He2 in Hinv2.
  have Htable2 : writeSuccessWithdrawalsInstructionTable global2 by
    (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  destruct (writeSuccessEncoderIntCaller156c0 global2 Htable2) as
    (Halign2 & trace2 & Hcode2).
  have Hx2second := writeSuccessWithdrawalsEncoderIntEndpointX2 regs2 global2
    sp (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal)
    trace2 Halign2 Hcode2.
  have HoRegs := f_equal (fun machine => machine.1.(seq_regs)) Ho.
  cbn in HoRegs.
  have Hout2 : outputRegs !! "x2" = Some (RVal_Bits sp).
  { rewrite <- HoRegs. unfold writeSuccessWithdrawalsOutputEntry,
      writeSuccessWithdrawalsSecondEncoderEndpoint. cbn.
    rewrite writeSuccess156ccRegsLookupOther; try discriminate.
    rewrite writeSuccess156c8RegsLookupOther; try discriminate.
    rewrite writeSuccess156c4RegsLookupOther; try discriminate.
    rewrite writeSuccess156c0RegsLookupOther; try discriminate.
    exact Hx2second. }
  have HfinalInv := writeSuccessWithdrawals156d0FinalEncoderInv args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 outputRegs outputGlobal
    (writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp
      withdrawal)
    (writeSuccessWithdrawalsIndexValue withdrawal)
    (writeSuccessWithdrawalsValidatorValue withdrawal) Hinv
    (writeSuccessFinalAddressOutputGlobal args sp pointer base total processed
      remaining withdrawal allBytes prefix current suffix scratch encoderScratch
      registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2
      global2 outputRegs outputGlobal Hinv Hp He1 He2 Ho)
    eq_refl Hout2 HoutputInv.
  rewrite Hfinal in HfinalInv.
  have HfactsFinal : writeSuccessWithdrawalsOperationalRegisterFacts finalRegs by
    (unfold Inv_encoder_int in HfinalInv; cbn in HfinalInv; tauto).
  have HtableFinal : writeSuccessWithdrawalsInstructionTable finalGlobal by
    (unfold Inv_encoder_int in HfinalInv; cbn in HfinalInv; tauto).
  destruct (writeSuccessEncoderIntCaller156dc finalGlobal HtableFinal) as
    (Halign & trace & Hcode).
  have Hx2 := writeSuccessWithdrawalsEncoderIntEndpointX2 finalRegs finalGlobal
    sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal)
    trace Halign Hcode.
  have HfactsNamed := writeSuccessEncoderIntEndpointFacts finalRegs sp
    (Z_to_bv 64 0x156dc) HfactsFinal.
  have Hexact := writeSuccessEncoderIntEndpointExact finalRegs finalGlobal sp
    (writeSuccessWithdrawalsAmountValue withdrawal) (Z_to_bv 64 0x156dc)
    trace Halign
    ltac:(rewrite writeSuccessWithdrawalsEncoderIntGlobal2Instrs; exact Hcode).
  have HregsEnd :
      (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
        (Z_to_bv 64 0x156dc)
        (writeSuccessWithdrawalsAmountValue withdrawal)).1.(seq_regs) =
      writeSuccessEncoderIntEndpointRegs finalRegs sp (Z_to_bv 64 0x156dc) by
    (unfold writeSuccessWithdrawalsEncoderIntEndpoint;
     exact (f_equal (fun machine => machine.1.(seq_regs)) Hexact)).
  have HfactsEnd : writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
        (Z_to_bv 64 0x156dc)
        (writeSuccessWithdrawalsAmountValue withdrawal)).1.(seq_regs) by
    (rewrite HregsEnd; exact HfactsNamed).
  split; assumption.
Qed.

Print Assumptions writeSuccessWithdrawalsFinalEncoderEndpointStateFacts.
