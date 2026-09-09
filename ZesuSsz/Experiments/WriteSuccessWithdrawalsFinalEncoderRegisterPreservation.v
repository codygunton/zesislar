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

Open Scope Z_scope.
Local Definition finalPreservationLookup (regs : reg_map) (register : string) :
    option valu :=
  @lookup string valu reg_map (@gmap_lookup string _ _ valu) register regs.

Lemma writeSuccessFinalEndpointLookup args sp pointer base total processed
    remaining withdrawal allBytes prefix current suffix scratch encoderScratch
    registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2
    global2 outputRegs outputGlobal finalRegs finalGlobal register value :
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
  register <> "PC" -> register <> "x1" -> register <> "x2" ->
  register <> "x5" -> register <> "x6" -> register <> "x10" ->
  register <> "x11" -> register <> "x12" -> register <> "x13" ->
  register <> "x14" -> register <> "x15" ->
  state.1.1.(seq_regs) !! register = Some value ->
  (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
    (Z_to_bv 64 0x156dc)
    (writeSuccessWithdrawalsAmountValue withdrawal)).1.(seq_regs) !! register =
    Some value.
Proof.
  intros Hinv Hp He1 He2 Ho Hfinal Hpc Hx1 Hx2 Hx5 Hx6 Hx10 Hx11 Hx12
    Hx13 Hx14 Hx15 Hlookup.
  change (finalPreservationLookup state.1.1.(seq_regs) register = Some value)
    in Hlookup.
  have Hprefix := f_equal (fun machine => finalPreservationLookup
    machine.1.(seq_regs) register) Hp.
  have Hentry1 := f_equal (fun machine => finalPreservationLookup
    machine.1.(seq_regs) register) He1.
  have Hentry2 := f_equal (fun machine => finalPreservationLookup
    machine.1.(seq_regs) register) He2.
  have Houtput := f_equal (fun machine => finalPreservationLookup
    machine.1.(seq_regs) register) Ho.
  have HfinalRegs := f_equal (fun machine => finalPreservationLookup
    machine.1.(seq_regs) register) Hfinal.
  unfold finalPreservationLookup in Hprefix, Hentry1, Hentry2, Houtput,
    HfinalRegs, Hlookup. cbn in Hprefix, Hentry1, Hentry2, Houtput, HfinalRegs.
  unfold writeSuccessWithdrawalsPrefixAfter,
    writeSuccessWithdrawalsPrefixStatea4,
    writeSuccessWithdrawalsPrefixStatea0,
    writeSuccessWithdrawalsPrefixState9c,
    writeSuccessWithdrawalsPrefixState98,
    writeSuccess156a4After, writeSuccess156a0After, writeSuccess1569cAfter,
    writeSuccess15698After, writeSuccess15694After in Hprefix.
  rewrite writeSuccess156a4RegsLookupOther in Hprefix; [|exact Hpc|exact Hx1].
  rewrite writeSuccess156a0RegsLookupOther in Hprefix; [|exact Hpc|exact Hx1].
  rewrite writeSuccess1569cRegsLookupOther in Hprefix; [|exact Hpc|exact Hx11].
  rewrite writeSuccess15698RegsLookupOther in Hprefix; [|exact Hpc|exact Hx12].
  rewrite writeSuccess15694RegsLookupOther in Hprefix; [|exact Hpc|exact Hx10].
  rewrite Hlookup in Hprefix.
  unfold writeSuccessWithdrawalsEncoderInt156b4State in Hentry1.
  cbn in Hentry1.
  rewrite writeSuccess156b0RegsLookupOther in Hentry1; [|exact Hpc|exact Hx1].
  rewrite writeSuccess156acRegsLookupOther in Hentry1; [|exact Hpc|exact Hx1].
  rewrite writeSuccess156a8RegsLookupOther in Hentry1;
    [|exact Hpc|exact Hx10].
  unfold writeSuccessWithdrawals156a8Regs in Hentry1.
  rewrite writeSuccessMemcpyEndpointLookupOther in Hentry1;
    [|exact Hpc|exact Hx13|exact Hx14|exact Hx15].
  rewrite <- Hprefix in Hentry1.
  unfold writeSuccessWithdrawalsSecondEncoderEntry in Hentry2. cbn in Hentry2.
  rewrite writeSuccess156bcRegsLookupOther in Hentry2; [|exact Hpc|exact Hx1].
  rewrite writeSuccess156b8RegsLookupOther in Hentry2; [|exact Hpc|exact Hx1].
  rewrite writeSuccess156b4RegsLookupOther in Hentry2;
    [|exact Hpc|exact Hx10].
  unfold writeSuccessWithdrawalsFirstEncoderEndpoint in Hentry2.
  have Hinv1 := writeSuccessWithdrawals156a8EncoderIntInv args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 Hinv
    Hp.
  rewrite He1 in Hinv1.
  have Htable1 : writeSuccessWithdrawalsInstructionTable global1 by
    (unfold Inv_encoder_int in Hinv1; cbn in Hinv1; tauto).
  destruct (writeSuccessEncoderIntCaller156b4 global1 Htable1) as
    (Halign1 & trace1 & Hcode1).
  rewrite (writeSuccessWithdrawalsEncoderIntEndpointLookupOther regs1 global1
    sp (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)
    trace1 register Halign1 Hcode1 Hpc Hx1 Hx2 Hx5 Hx10 Hx11) in Hentry2.
  rewrite <- Hentry1 in Hentry2.
  unfold writeSuccessWithdrawalsOutputEntry in Houtput. cbn in Houtput.
  rewrite writeSuccess156ccRegsLookupOther in Houtput; [|exact Hpc|exact Hx1].
  rewrite writeSuccess156c8RegsLookupOther in Houtput; [|exact Hpc|exact Hx1].
  rewrite writeSuccess156c4RegsLookupOther in Houtput; [|exact Hpc|exact Hx10].
  rewrite writeSuccess156c0RegsLookupOther in Houtput; [|exact Hpc|exact Hx11].
  unfold writeSuccessWithdrawalsSecondEncoderEndpoint in Houtput.
  have Hinv2 := writeSuccessWithdrawals156b4SecondEncoderInv args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 Hinv Hp He1.
  rewrite He2 in Hinv2.
  have Htable2 : writeSuccessWithdrawalsInstructionTable global2 by
    (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  destruct (writeSuccessEncoderIntCaller156c0 global2 Htable2) as
    (Halign2 & trace2 & Hcode2).
  rewrite (writeSuccessWithdrawalsEncoderIntEndpointLookupOther regs2 global2
    sp (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal)
    trace2 register Halign2 Hcode2 Hpc Hx1 Hx2 Hx5 Hx10 Hx11) in Houtput.
  rewrite <- Hentry2 in Houtput.
  cbn in HfinalRegs.
  rewrite writeSuccess156d8RegsLookupOther in HfinalRegs; [|exact Hpc|exact Hx1].
  rewrite writeSuccess156d4RegsLookupOther in HfinalRegs; [|exact Hpc|exact Hx1].
  rewrite writeSuccess156d0RegsLookupOther in HfinalRegs; [|exact Hpc|exact Hx10].
  rewrite writeSuccessOutputEndpointLookupOther in HfinalRegs;
    [|exact Hpc|exact Hx5].
  rewrite <- Houtput in HfinalRegs.
  have Hpackage := writeSuccessWithdrawalsFinalEncoderEndpointPackage args sp
    pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 regs2 global2 outputRegs outputGlobal finalRegs
    finalGlobal Hinv Hp He1 He2 Ho Hfinal.
  cbn in Hpackage.
  destruct Hpackage as (_ & _ & _ & _ & _ & HtableEnd & _ & _ &
    HglobalEnd).
  have HtableFinal : writeSuccessWithdrawalsInstructionTable finalGlobal.
  { rewrite HglobalEnd in HtableEnd.
    unfold writeSuccessWithdrawalsInstructionTable in HtableEnd |- *.
    intros pc trace Hsource.
    rewrite writeSuccessWithdrawalsEncoderIntGlobal2Instrs in HtableEnd.
    apply HtableEnd. exact Hsource. }
  destruct (writeSuccessEncoderIntCaller156dc finalGlobal HtableFinal) as
    (Halign3 & trace3 & Hcode3).
  rewrite (writeSuccessWithdrawalsEncoderIntEndpointLookupOther finalRegs
    finalGlobal sp (Z_to_bv 64 0x156dc)
    (writeSuccessWithdrawalsAmountValue withdrawal) trace3 register Halign3
    Hcode3 Hpc Hx1 Hx2 Hx5 Hx10 Hx11).
  symmetry. exact HfinalRegs.
Qed.


Print Assumptions writeSuccessFinalEndpointLookup.
