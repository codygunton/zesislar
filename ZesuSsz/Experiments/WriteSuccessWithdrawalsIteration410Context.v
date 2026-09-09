From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_95.a156dc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156cc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156dc.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntCallerFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalEncoderEndpointFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalAmountRead.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInvContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156d0FinalEncoderInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationThroughFinalEncoder.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOutputEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.

Lemma writeSuccessWithdrawals407EndpointTailFacts args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 outputRegs outputGlobal finalRegs finalGlobal :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer = writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current withdrawal = writeSuccess15d10Before regs1 global1 ->
  writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal = writeSuccess15d10Before regs2 global2 ->
  writeSuccessWithdrawalsOutputEntry (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs) (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).2 (sp + BV 64 1768)%bv = writeSuccess10190Before outputRegs outputGlobal ->
  writeSuccess156d8After (writeSuccess156d4Regs (writeSuccess156d0Regs (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0)) (writeSuccessWithdrawalsAmountValue withdrawal))) outputGlobal = writeSuccess15d10Before finalRegs finalGlobal ->
  writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal) =
      writeSuccess156dcBefore
        (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal)).1.(seq_regs)
        (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal)).2 /\
    (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal)).1.(seq_regs) !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156dc)) /\
    (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal)).1.(seq_regs) !! "x8" = Some (RVal_Bits pointer) /\
    (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal)).1.(seq_regs) !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) /\
    eval_a_exp (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal)).1.(seq_regs) writeSuccess156dcMstatus = Some (Val_Bool true) /\
    writeSuccessWithdrawalsInstructionTable (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal)).2.
Proof.
  intros Hinv Hp He1 He2 Ho HfinalEntry.
  have Hpackage := writeSuccessWithdrawalsFinalEncoderEndpointPackage args sp
    pointer base total processed (S remaining) withdrawal allBytes prefix
    current suffix scratch encoderScratch registerFrame memoryFrame priorLog
    state regs0 global0 regs1 global1 regs2 global2 outputRegs outputGlobal
    finalRegs finalGlobal Hinv Hp He1 He2 Ho HfinalEntry.
  cbn in Hpackage.
  destruct Hpackage as
    (HpcEndpoint & Hx8Endpoint & Hx9Endpoint & Hx18Endpoint &
     HmstatusEndpoint & HtableEndpoint & HlowFrame & HmemoryFrame &
     HglobalEndpoint).
  destruct (writeSuccessWithdrawalsSecondEncoderEndpointIterationRegisters args sp pointer base total processed (S remaining) withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 Hinv Hp He1 He2) as (Hx8s & Hx9s & Hx18s).
  have HoRegs := f_equal (fun machine => machine.1.(seq_regs)) Ho. cbn in HoRegs.
  have Hout8 : outputRegs !! "x8" = Some (RVal_Bits pointer).
  { rewrite <- HoRegs. unfold writeSuccessWithdrawalsOutputEntry. cbn.
    rewrite writeSuccess156ccRegsLookupOther; try discriminate. rewrite writeSuccess156c8RegsLookupOther; try discriminate.
    rewrite writeSuccess156c4RegsLookupOther; try discriminate. rewrite writeSuccess156c0RegsLookupOther; try discriminate. exact Hx8s. }
  have Hout9 : outputRegs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { rewrite <- HoRegs. unfold writeSuccessWithdrawalsOutputEntry. cbn.
    rewrite writeSuccess156ccRegsLookupOther; try discriminate. rewrite writeSuccess156c8RegsLookupOther; try discriminate.
    rewrite writeSuccess156c4RegsLookupOther; try discriminate. rewrite writeSuccess156c0RegsLookupOther; try discriminate. exact Hx9s. }
  have HfinalRegsEq := f_equal (fun machine => machine.1.(seq_regs)) HfinalEntry. cbn in HfinalRegsEq.
  have Hfinal8 : finalRegs !! "x8" = Some (RVal_Bits pointer).
  { rewrite <- HfinalRegsEq. cbn. rewrite writeSuccess156d8RegsLookupOther; try discriminate.
    rewrite writeSuccess156d4RegsLookupOther; try discriminate. rewrite writeSuccess156d0RegsLookupOther; try discriminate.
    rewrite writeSuccessOutputEndpointLookupOther; try discriminate. exact Hout8. }
  have Hfinal9 : finalRegs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { rewrite <- HfinalRegsEq. cbn. rewrite writeSuccess156d8RegsLookupOther; try discriminate.
    rewrite writeSuccess156d4RegsLookupOther; try discriminate. rewrite writeSuccess156d0RegsLookupOther; try discriminate.
    rewrite writeSuccessOutputEndpointLookupOther; try discriminate. exact Hout9. }
  have Hglobal := writeSuccessWithdrawalsAddressOutputGlobal args sp pointer base total processed (S remaining) withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 outputRegs outputGlobal Hinv Hp He1 He2 Ho.
  have HoutInv := writeSuccessWithdrawals156c0OutputInv args sp pointer base total processed (S remaining) withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 Hinv Hp He1 He2. rewrite Ho in HoutInv.
  have Hx2 : outputRegs !! "x2" = Some (RVal_Bits sp).
  { have Hinv2 := writeSuccessWithdrawals156b4SecondEncoderInv args sp pointer base total processed (S remaining) withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 Hinv Hp He1. rewrite He2 in Hinv2.
    have Htable2 : writeSuccessWithdrawalsInstructionTable global2 by (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
    destruct (writeSuccessEncoderIntCaller156c0 global2 Htable2) as (Ha & tr & Hc).
    have Hx2s := writeSuccessWithdrawalsEncoderIntEndpointX2 regs2 global2 sp (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal) tr Ha Hc.
    rewrite <- HoRegs. unfold writeSuccessWithdrawalsOutputEntry, writeSuccessWithdrawalsSecondEncoderEndpoint. cbn.
    rewrite writeSuccess156ccRegsLookupOther; try discriminate. rewrite writeSuccess156c8RegsLookupOther; try discriminate.
    rewrite writeSuccess156c4RegsLookupOther; try discriminate. rewrite writeSuccess156c0RegsLookupOther; try discriminate. exact Hx2s. }
  have Hfinv := writeSuccessWithdrawals156d0FinalEncoderInv args sp pointer base total processed (S remaining) withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 outputRegs outputGlobal (writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp withdrawal) (writeSuccessWithdrawalsIndexValue withdrawal) (writeSuccessWithdrawalsValidatorValue withdrawal) Hinv Hglobal eq_refl Hx2 HoutInv.
  rewrite HfinalEntry in Hfinv.
  have Htable : writeSuccessWithdrawalsInstructionTable finalGlobal by (unfold Inv_encoder_int in Hfinv; cbn in Hfinv; tauto).
  have Hfacts : writeSuccessWithdrawalsOperationalRegisterFacts finalRegs by (unfold Inv_encoder_int in Hfinv; cbn in Hfinv; tauto).
  destruct (writeSuccessEncoderIntCaller156dc finalGlobal Htable) as (Halign & finalTrace & Hcode).
  have HendFacts := writeSuccessEncoderIntEndpointFacts finalRegs sp (Z_to_bv 64 0x156dc) Hfacts.
  have Hpc := writeSuccessWithdrawalsEncoderIntEndpointPc finalRegs finalGlobal sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal) finalTrace Halign Hcode.
  have HglobalEnd := writeSuccessWithdrawalsEncoderIntEndpointGlobal finalRegs finalGlobal sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal) finalTrace Halign Hcode.
  have Hexact := writeSuccessEncoderIntEndpointExact finalRegs finalGlobal sp (writeSuccessWithdrawalsAmountValue withdrawal) (Z_to_bv 64 0x156dc) finalTrace Halign ltac:(rewrite writeSuccessWithdrawalsEncoderIntGlobal2Instrs; exact Hcode).
  have HregsEq : (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal)).1.(seq_regs) = writeSuccessEncoderIntEndpointRegs finalRegs sp (Z_to_bv 64 0x156dc) by (unfold writeSuccessWithdrawalsEncoderIntEndpoint; exact (f_equal (fun machine => machine.1.(seq_regs)) Hexact)).
  repeat split.
  - unfold writeSuccessWithdrawalsEncoderIntEndpoint. rewrite Hexact.
    have Hdc : finalGlobal.(seq_instrs) !! Z_to_bv 64 0x156dc = Some a156dc by (apply Htable; cbn; tauto).
    have -> : finalTrace = a156dc by congruence. reflexivity.
  - exact HpcEndpoint.
  - rewrite HregsEq. rewrite writeSuccessEncoderIntEndpointLookupOther; try discriminate. exact Hfinal8.
  - rewrite HregsEq. rewrite writeSuccessEncoderIntEndpointLookupOther; try discriminate. exact Hfinal9.
  - rewrite HregsEq. exact (proj1 HendFacts).
  - rewrite HglobalEnd. unfold writeSuccessWithdrawalsInstructionTable in Htable |- *. intros pc trace Hin. apply Htable. exact Hin.
Qed.

Print Assumptions writeSuccessWithdrawals407EndpointTailFacts.

