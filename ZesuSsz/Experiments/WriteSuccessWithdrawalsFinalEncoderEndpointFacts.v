From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
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
Require Import ZesuSsz.Experiments.WriteSuccessSegment156dc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntFrame.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntCallerFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalAmountRead.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInvContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156d0FinalEncoderInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHelperMemoryFrame.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationOutputData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyAfter.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpyMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpyState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpySupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOutputEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.

Open Scope Z_scope.
Local Definition writeSuccessFinalRegLookup (regs : reg_map) (register : string) :
    option valu :=
  @lookup string valu reg_map (@gmap_lookup string _ _ valu) register regs.

Definition writeSuccessWithdrawalsFinalEncoderEntry outputRegs global
    (sp : bv 64)
    (withdrawal : WriteSuccessObservation.WriteSuccessWithdrawalObservation) :
    WriteSuccessWithdrawalsConcreteState :=
  (writeSuccess156d8After
    (writeSuccess156d4Regs
      (writeSuccess156d0Regs
        (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0))
        (writeSuccessWithdrawalsAmountValue withdrawal))) global, []).

Definition writeSuccessWithdrawalsFinalEncoderEndpoint outputRegs global
    (sp : bv 64)
    (withdrawal : WriteSuccessObservation.WriteSuccessWithdrawalObservation) :=
  writeSuccessWithdrawalsEncoderIntEndpoint
    (writeSuccessWithdrawalsFinalEncoderEntry outputRegs global sp withdrawal).1.1.(seq_regs)
    global sp (Z_to_bv 64 0x156dc)
    (writeSuccessWithdrawalsAmountValue withdrawal).

Lemma writeSuccessWithdrawalsSecondEncoderEndpointIterationRegisters args sp
    pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 regs2 global2 :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
    withdrawal = writeSuccess15d10Before regs1 global1 ->
  writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal =
    writeSuccess15d10Before regs2 global2 ->
  (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs) !! "x8" =
      Some (RVal_Bits pointer) /\
  (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat remaining))) /\
  (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs) !! "x18" =
      Some (RVal_Bits (sp + BV 64 1768)%bv).
Proof.
  intros Hinv Hprefix Hentry1 Hentry2.
  have Hx8 : state.1.1.(seq_regs) !! "x8" = Some (RVal_Bits pointer) by
    (unfold Inv_15694 in Hinv; tauto).
  have Hx9 : state.1.1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat remaining))) by
    (unfold Inv_15694 in Hinv; tauto).
  have Hx18 := writeSuccessWithdrawalsSecondEncoderEndpointX18 args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 regs2 global2 Hinv Hprefix Hentry1 Hentry2.
  have preserve (register : string) (value : valu) :
      register <> "PC" -> register <> "x1" -> register <> "x2" ->
      register <> "x5" -> register <> "x6" -> register <> "x10" ->
      register <> "x11" -> register <> "x12" -> register <> "x13" ->
      register <> "x14" -> register <> "x15" ->
      state.1.1.(seq_regs) !! register = Some value ->
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs) !! register = Some value.
  { intros Hpc Hx1 Hx2 Hx5 Hx6 Hx10 Hx11 Hx12 Hx13 Hx14 Hx15 Hregister.
    change (writeSuccessFinalRegLookup state.1.1.(seq_regs) register =
      Some value) in Hregister.
    have Hp :
      writeSuccessFinalRegLookup
        (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer).1.(seq_regs)
        register = writeSuccessFinalRegLookup regs0 register :=
      f_equal (fun machine => writeSuccessFinalRegLookup
        machine.1.(seq_regs) register) Hprefix.
    have He1 :
      writeSuccessFinalRegLookup
        (writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer
          current withdrawal).1.(seq_regs) register =
        writeSuccessFinalRegLookup regs1 register :=
      f_equal (fun machine => writeSuccessFinalRegLookup
        machine.1.(seq_regs) register) Hentry1.
    have He2 :
      writeSuccessFinalRegLookup
        (writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp
          withdrawal).1.(seq_regs) register =
        writeSuccessFinalRegLookup regs2 register :=
      f_equal (fun machine => writeSuccessFinalRegLookup
        machine.1.(seq_regs) register) Hentry2.
    unfold writeSuccessFinalRegLookup in Hp, He1, He2, Hregister.
    cbn in Hp, He1, He2.
    unfold writeSuccessWithdrawalsPrefixAfter,
      writeSuccessWithdrawalsPrefixStatea4,
      writeSuccessWithdrawalsPrefixStatea0,
      writeSuccessWithdrawalsPrefixState9c,
      writeSuccessWithdrawalsPrefixState98,
      writeSuccess156a4After, writeSuccess156a0After,
      writeSuccess1569cAfter, writeSuccess15698After,
      writeSuccess15694After in Hp.
    rewrite writeSuccess156a4RegsLookupOther in Hp; [|exact Hpc|exact Hx1].
    rewrite writeSuccess156a0RegsLookupOther in Hp; [|exact Hpc|exact Hx1].
    rewrite writeSuccess1569cRegsLookupOther in Hp; [|exact Hpc|exact Hx11].
    rewrite writeSuccess15698RegsLookupOther in Hp; [|exact Hpc|exact Hx12].
    rewrite writeSuccess15694RegsLookupOther in Hp; [|exact Hpc|exact Hx10].
    rewrite Hregister in Hp.
    unfold writeSuccessWithdrawalsEncoderInt156b4State in He1. cbn in He1.
    rewrite writeSuccess156b0RegsLookupOther in He1; [|exact Hpc|exact Hx1].
    rewrite writeSuccess156acRegsLookupOther in He1; [|exact Hpc|exact Hx1].
    rewrite writeSuccess156a8RegsLookupOther in He1; [|exact Hpc|exact Hx10].
    unfold writeSuccessWithdrawals156a8Regs in He1.
    rewrite writeSuccessMemcpyEndpointLookupOther in He1;
      [|exact Hpc|exact Hx13|exact Hx14|exact Hx15].
    rewrite <- Hp in He1.
    unfold writeSuccessWithdrawalsSecondEncoderEntry in He2. cbn in He2.
    rewrite writeSuccess156bcRegsLookupOther in He2; [|exact Hpc|exact Hx1].
    rewrite writeSuccess156b8RegsLookupOther in He2; [|exact Hpc|exact Hx1].
    rewrite writeSuccess156b4RegsLookupOther in He2; [|exact Hpc|exact Hx10].
    unfold writeSuccessWithdrawalsFirstEncoderEndpoint in He2.
    have Hinv1 := writeSuccessWithdrawals156a8EncoderIntInv args sp pointer base
      total processed remaining withdrawal allBytes prefix current suffix scratch
      encoderScratch registerFrame memoryFrame priorLog state regs0 global0 Hinv
      Hprefix.
    rewrite Hentry1 in Hinv1.
    have Htable1 : writeSuccessWithdrawalsInstructionTable global1 by
      (unfold Inv_encoder_int in Hinv1; cbn in Hinv1; tauto).
    destruct (writeSuccessEncoderIntCaller156b4 global1 Htable1) as
      (Halign1 & trace1 & Hcode1).
    rewrite (writeSuccessWithdrawalsEncoderIntEndpointLookupOther regs1 global1
      sp (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)
      trace1 register Halign1 Hcode1 Hpc Hx1 Hx2 Hx5 Hx10 Hx11) in He2.
    rewrite <- He1 in He2.
    unfold writeSuccessWithdrawalsSecondEncoderEndpoint.
    have Hinv2 := writeSuccessWithdrawals156b4SecondEncoderInv args sp pointer
      base total processed remaining withdrawal allBytes prefix current suffix
      scratch encoderScratch registerFrame memoryFrame priorLog state regs0
      global0 regs1 global1 Hinv Hprefix Hentry1.
    rewrite Hentry2 in Hinv2.
    have Htable2 : writeSuccessWithdrawalsInstructionTable global2 by
      (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
    destruct (writeSuccessEncoderIntCaller156c0 global2 Htable2) as
      (Halign2 & trace2 & Hcode2).
    rewrite (writeSuccessWithdrawalsEncoderIntEndpointLookupOther regs2 global2
      sp (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal)
      trace2 register Halign2 Hcode2 Hpc Hx1 Hx2 Hx5 Hx10 Hx11).
    symmetry. exact He2. }
  split; first (apply preserve; try discriminate; exact Hx8).
  split; first (apply preserve; try discriminate; exact Hx9).
  exact Hx18.
Qed.

Lemma writeSuccessFinalAddressOutputGlobal args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 outputRegs outputGlobal :
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
  outputGlobal = writeSuccessEncoderIntGlobal2
    (writeSuccessEncoderIntGlobal2
      (writeSuccessWithdrawals156a8Global regs0 global0 sp pointer current) sp
      (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)) sp
    (Z_to_bv 64 0x156c0)
    (writeSuccessWithdrawalsValidatorValue withdrawal).
Proof.
  intros Hinv Hprefix Hentry1 Hentry2 Houtput.
  have Hinv1 := writeSuccessWithdrawals156a8EncoderIntInv args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 Hinv
    Hprefix.
  rewrite Hentry1 in Hinv1.
  have Htable1 : writeSuccessWithdrawalsInstructionTable global1 by
    (unfold Inv_encoder_int in Hinv1; cbn in Hinv1; tauto).
  destruct (writeSuccessEncoderIntCaller156b4 global1 Htable1) as
    (Halign1 & trace1 & Hcode1).
  have Hglobal1 := writeSuccessWithdrawalsEncoderIntEndpointGlobal regs1 global1
    sp (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)
    trace1 Halign1 Hcode1.
  have Hinv2 := writeSuccessWithdrawals156b4SecondEncoderInv args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 Hinv Hprefix Hentry1.
  rewrite Hentry2 in Hinv2.
  have Htable2 : writeSuccessWithdrawalsInstructionTable global2 by
    (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  destruct (writeSuccessEncoderIntCaller156c0 global2 Htable2) as
    (Halign2 & trace2 & Hcode2).
  have Hglobal2 := writeSuccessWithdrawalsEncoderIntEndpointGlobal regs2 global2
    sp (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal)
    trace2 Halign2 Hcode2.
  have He1 := f_equal snd Hentry1. cbn in He1.
  have He2 := f_equal snd Hentry2. cbn in He2.
  have Ho := f_equal snd Houtput. cbn in Ho.
  unfold writeSuccessWithdrawalsOutputEntry in Ho. cbn in Ho.
  unfold writeSuccessWithdrawalsSecondEncoderEndpoint in Ho.
  rewrite Hglobal2 in Ho. rewrite <- He2, Hglobal1, <- He1 in Ho.
  symmetry. exact Ho.
Qed.

Local Lemma writeSuccessFinalHighScratchMemoryFrame args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsMemoryFrame sp
    (writeSuccessWithdrawals156a8Global regs0 global0 sp pointer
      current).(seq_mem) memoryFrame.
Proof.
  intros Hinv Hprefix.
  have Houter : writeSuccessWithdrawalsMemoryFrame sp state.1.2.(seq_mem)
      memoryFrame by (unfold Inv_15694 in Hinv; tauto).
  have Hglobal0 : global0 = state.1.2.
  { have H := f_equal snd Hprefix. cbn in H. symmetry. exact H. }
  have Hlength : length current = 48%nat by
    (unfold Inv_15694 in Hinv; tauto).
  destruct (writeSuccessWithdrawalsPrefix15694MemcpyMemory args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state Hinv) as
    (_ & _ & Hrange & _ & _ & _ & _ & _ & Hbacked & _).
  have Hmemory := writeSuccessMemcpyBytesAfterMemory
    (writeSuccess101d4Regs regs0) global0 pointer
    (sp + BV 64 1744)%bv (Z_to_bv 64 0) current 0
    ltac:(reflexivity)
    ltac:(unfold islaMemoryRange in Hrange; lia).
  specialize (Hmemory
    ltac:(unfold islaMemoryRange in Hrange; cbn in Hrange; lia)).
  have HglobalMemory :
      (writeSuccessWithdrawals156a8Global regs0 global0 sp pointer
        current).(seq_mem) =
      write_mem_list global0.(seq_mem)
        (Z_to_bv 64 (bv_unsigned (sp + BV 64 1744)%bv)) current.
  { unfold writeSuccessWithdrawals156a8Global, writeSuccessMemcpyEndpointGlobal,
      writeSuccessMemcpyLoopAfter. rewrite Hmemory. cbn.
    replace ((sp + BV 64 1744)%bv + Z_to_bv 64 0)%bv with
        (Z_to_bv 64 (bv_unsigned (sp + BV 64 1744)%bv)) by
      (apply bv_eq; bv_solve).
    reflexivity. }
  have HstartFrame : writeSuccessMemoryRangeFrame
      (bv_unsigned (sp + BV 64 1744)%bv) (length current)
      global0.(seq_mem) state.1.2.(seq_mem).
  { rewrite Hglobal0. split; first reflexivity. intros address _. reflexivity. }
  have Hbacked0 : forall location,
      bv_unsigned (sp + BV 64 1744)%bv <= location <
        bv_unsigned (sp + BV 64 1744)%bv + Z.of_nat (length current) ->
      is_Some (global0.(seq_mem) !! Z_to_bv 64 location).
  { intros location Hlocation. rewrite Hglobal0. apply Hbacked.
    exact Hlocation. }
  have HhighFrame := writeSuccessMemoryRangeFrameWrite global0.(seq_mem)
    state.1.2.(seq_mem) (bv_unsigned (sp + BV 64 1744)%bv) current
    HstartFrame Hrange Hbacked0.
  rewrite <- HglobalMemory in HhighFrame.
  apply writeSuccessWithdrawalsMemoryFrameHighScratch with
    (before := state.1.2.(seq_mem)); first exact Houter.
  have Hdestination := writeSuccessWithdrawalsPrefixDestinationUnsigned sp
    ltac:(unfold Inv_15694 in Hinv; tauto).
  rewrite <- Hdestination. rewrite <- Hlength. exact HhighFrame.
Qed.

Local Lemma writeSuccessFinalOutputMemoryFrame args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 outputRegs outputGlobal :
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
  writeSuccessWithdrawalsMemoryFrame sp outputGlobal.(seq_mem) memoryFrame.
Proof.
  intros Hinv Hprefix Hentry1 Hentry2 Houtput.
  have Hhigh := writeSuccessFinalHighScratchMemoryFrame args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 Hinv
    Hprefix.
  have He1 := f_equal snd Hentry1. cbn in He1.
  have Houter1 : writeSuccessWithdrawalsMemoryFrame sp global1.(seq_mem)
      memoryFrame by (rewrite <- He1; exact Hhigh).
  have Hinv1 := writeSuccessWithdrawals156a8EncoderIntInv args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 Hinv
    Hprefix.
  rewrite Hentry1 in Hinv1.
  have Hrange1 : islaMemoryRange (bv_unsigned sp - 16) 16 by
    (unfold Inv_encoder_int in Hinv1; cbn in Hinv1; tauto).
  have Hbacked1 : forall location,
      bv_unsigned sp - 16 <= location < bv_unsigned sp ->
      is_Some (global1.(seq_mem) !! Z_to_bv 64 location) by
    (unfold Inv_encoder_int in Hinv1; cbn in Hinv1; tauto).
  have Htable1 : writeSuccessWithdrawalsInstructionTable global1 by
    (unfold Inv_encoder_int in Hinv1; cbn in Hinv1; tauto).
  destruct (writeSuccessEncoderIntCaller156b4 global1 Htable1) as
    (Halign1 & trace1 & Hcode1).
  have HendpointGlobal1 := writeSuccessWithdrawalsEncoderIntEndpointGlobal
    regs1 global1 sp (Z_to_bv 64 0x156b4)
    (writeSuccessWithdrawalsIndexValue withdrawal) trace1 Halign1 Hcode1.
  have Hframe1 := writeSuccessEncoderIntGlobal2Frame global1 global1.(seq_mem)
    sp (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)
    Hrange1 Hbacked1 ltac:(split; [reflexivity|intros; reflexivity]).
  have He2 := f_equal snd Hentry2. cbn in He2.
  unfold writeSuccessWithdrawalsSecondEncoderEntry,
    writeSuccessWithdrawalsFirstEncoderEndpoint in He2.
  rewrite HendpointGlobal1 in He2.
  have Hframe1' : writeSuccessMemoryRangeFrame (bv_unsigned sp - 16) 16
      global2.(seq_mem) global1.(seq_mem).
  { rewrite <- He2. exact Hframe1. }
  have Houter2 : writeSuccessWithdrawalsMemoryFrame sp global2.(seq_mem)
      memoryFrame := writeSuccessWithdrawalsMemoryFrameLowScratch sp
        global1.(seq_mem) global2.(seq_mem) memoryFrame Houter1 Hframe1'.
  have Hinv2 := writeSuccessWithdrawals156b4SecondEncoderInv args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 Hinv Hprefix Hentry1.
  rewrite Hentry2 in Hinv2.
  have Hrange2 : islaMemoryRange (bv_unsigned sp - 16) 16 by
    (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  have Hbacked2 : forall location,
      bv_unsigned sp - 16 <= location < bv_unsigned sp ->
      is_Some (global2.(seq_mem) !! Z_to_bv 64 location) by
    (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  have Htable2 : writeSuccessWithdrawalsInstructionTable global2 by
    (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  destruct (writeSuccessEncoderIntCaller156c0 global2 Htable2) as
    (Halign2 & trace2 & Hcode2).
  have HendpointGlobal2 := writeSuccessWithdrawalsEncoderIntEndpointGlobal
    regs2 global2 sp (Z_to_bv 64 0x156c0)
    (writeSuccessWithdrawalsValidatorValue withdrawal) trace2 Halign2 Hcode2.
  have Hframe2 := writeSuccessEncoderIntGlobal2Frame global2 global2.(seq_mem)
    sp (Z_to_bv 64 0x156c0)
    (writeSuccessWithdrawalsValidatorValue withdrawal) Hrange2 Hbacked2
    ltac:(split; [reflexivity|intros; reflexivity]).
  have Ho := f_equal snd Houtput. cbn in Ho.
  unfold writeSuccessWithdrawalsOutputEntry,
    writeSuccessWithdrawalsSecondEncoderEndpoint in Ho. cbn in Ho.
  rewrite HendpointGlobal2 in Ho.
  have Hframe2' : writeSuccessMemoryRangeFrame (bv_unsigned sp - 16) 16
      outputGlobal.(seq_mem) global2.(seq_mem).
  { rewrite <- Ho. exact Hframe2. }
  exact (writeSuccessWithdrawalsMemoryFrameLowScratch sp global2.(seq_mem)
    outputGlobal.(seq_mem) memoryFrame Houter2 Hframe2').
Qed.

Lemma writeSuccessWithdrawalsFinalEncoderEndpointPackage args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 outputRegs outputGlobal finalRegs finalGlobal :
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
        withdrawal).2
      (sp + BV 64 1768)%bv = writeSuccess10190Before outputRegs outputGlobal ->
  writeSuccess156d8After
      (writeSuccess156d4Regs
        (writeSuccess156d0Regs
          (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0))
          (writeSuccessWithdrawalsAmountValue withdrawal))) outputGlobal =
    writeSuccess15d10Before finalRegs finalGlobal ->
  let endpoint := writeSuccessWithdrawalsEncoderIntEndpoint finalRegs
    finalGlobal sp (Z_to_bv 64 0x156dc)
    (writeSuccessWithdrawalsAmountValue withdrawal) in
  endpoint.1.(seq_regs) !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x156dc)) /\
  endpoint.1.(seq_regs) !! "x8" = Some (RVal_Bits pointer) /\
  endpoint.1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat remaining))) /\
  endpoint.1.(seq_regs) !! "x18" =
      Some (RVal_Bits (sp + BV 64 1768)%bv) /\
  eval_a_exp endpoint.1.(seq_regs) writeSuccess156dcMstatus =
      Some (Val_Bool true) /\
  writeSuccessWithdrawalsInstructionTable endpoint.2 /\
  writeSuccessMemoryRangeFrame (bv_unsigned sp - 16) 16
      endpoint.2.(seq_mem) outputGlobal.(seq_mem) /\
  writeSuccessWithdrawalsMemoryFrame sp endpoint.2.(seq_mem) memoryFrame /\
  endpoint.2 = writeSuccessEncoderIntGlobal2 finalGlobal sp
      (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal).
Proof.
  intros Hinv Hprefix Hentry1 Hentry2 Houtput HfinalEntry. cbn.
  destruct (writeSuccessWithdrawalsSecondEncoderEndpointIterationRegisters
    args sp pointer base total processed remaining withdrawal allBytes prefix
    current suffix scratch encoderScratch registerFrame memoryFrame priorLog
    state regs0 global0 regs1 global1 regs2 global2 Hinv Hprefix Hentry1
    Hentry2) as (Hx8second & Hx9second & Hx18second).
  have HoutputRegs := f_equal (fun machine => machine.1.(seq_regs)) Houtput.
  cbn in HoutputRegs.
  have preserveOutput (register : string) (value : valu) :
      register <> "PC" -> register <> "x1" -> register <> "x10" ->
      register <> "x11" ->
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
        withdrawal).1.(seq_regs) !! register = Some value ->
      outputRegs !! register = Some value.
  { intros Hpc Hx1 Hx10 Hx11 Hlookup.
    rewrite <- HoutputRegs. unfold writeSuccessWithdrawalsOutputEntry. cbn.
    rewrite writeSuccess156ccRegsLookupOther; [|exact Hpc|exact Hx1].
    rewrite writeSuccess156c8RegsLookupOther; [|exact Hpc|exact Hx1].
    rewrite writeSuccess156c4RegsLookupOther; [|exact Hpc|exact Hx10].
    rewrite writeSuccess156c0RegsLookupOther; [|exact Hpc|exact Hx11].
    exact Hlookup. }
  have Hout8 := preserveOutput "x8" (RVal_Bits pointer)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) Hx8second.
  have Hout9 := preserveOutput "x9"
    (RVal_Bits (Z_to_bv 64 (Z.of_nat remaining)))
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) Hx9second.
  have Hout18 := preserveOutput "x18" (RVal_Bits (sp + BV 64 1768)%bv)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) Hx18second.
  have HfinalRegs := f_equal (fun machine => machine.1.(seq_regs)) HfinalEntry.
  cbn in HfinalRegs.
  have preserveFinal (register : string) (value : valu) :
      register <> "PC" -> register <> "x1" -> register <> "x5" ->
      register <> "x10" ->
      outputRegs !! register = Some value ->
      finalRegs !! register = Some value.
  { intros Hpc Hx1 Hx5 Hx10 Hlookup. rewrite <- HfinalRegs. cbn.
    rewrite writeSuccess156d8RegsLookupOther; [|exact Hpc|exact Hx1].
    rewrite writeSuccess156d4RegsLookupOther; [|exact Hpc|exact Hx1].
    rewrite writeSuccess156d0RegsLookupOther; [|exact Hpc|exact Hx10].
    rewrite writeSuccessOutputEndpointLookupOther; [|exact Hpc|exact Hx5].
    exact Hlookup. }
  have Hfinal8 := preserveFinal "x8" (RVal_Bits pointer)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) Hout8.
  have Hfinal9 := preserveFinal "x9"
    (RVal_Bits (Z_to_bv 64 (Z.of_nat remaining)))
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) Hout9.
  have Hfinal18 := preserveFinal "x18" (RVal_Bits (sp + BV 64 1768)%bv)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) Hout18.
  have Hglobal := writeSuccessFinalAddressOutputGlobal args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 regs2 global2 outputRegs outputGlobal Hinv Hprefix
    Hentry1 Hentry2 Houtput.
  have HoutputInv := writeSuccessWithdrawals156c0OutputInv args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 Hinv Hprefix Hentry1 Hentry2.
  rewrite Houtput in HoutputInv.
  have Hinv2 := writeSuccessWithdrawals156b4SecondEncoderInv args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 Hinv Hprefix Hentry1.
  rewrite Hentry2 in Hinv2.
  have Htable2 : writeSuccessWithdrawalsInstructionTable global2 by
    (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  destruct (writeSuccessEncoderIntCaller156c0 global2 Htable2) as
    (Halign2 & trace2 & Hcode2).
  have Hx2second := writeSuccessWithdrawalsEncoderIntEndpointX2 regs2 global2
    sp (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal)
    trace2 Halign2 Hcode2.
  have Hout2 : outputRegs !! "x2" = Some (RVal_Bits sp).
  { rewrite <- HoutputRegs. unfold writeSuccessWithdrawalsOutputEntry,
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
    (writeSuccessWithdrawalsValidatorValue withdrawal) Hinv Hglobal eq_refl
    Hout2 HoutputInv.
  rewrite HfinalEntry in HfinalInv.
  have Htable : writeSuccessWithdrawalsInstructionTable finalGlobal by
    (unfold Inv_encoder_int in HfinalInv; cbn in HfinalInv; tauto).
  have Hfacts : writeSuccessWithdrawalsOperationalRegisterFacts finalRegs by
    (unfold Inv_encoder_int in HfinalInv; cbn in HfinalInv; tauto).
  have Hrange : islaMemoryRange (bv_unsigned sp - 16) 16 by
    (unfold Inv_encoder_int in HfinalInv; cbn in HfinalInv; tauto).
  have Hbacked : forall location,
      bv_unsigned sp - 16 <= location < bv_unsigned sp ->
      is_Some (finalGlobal.(seq_mem) !! Z_to_bv 64 location) by
    (unfold Inv_encoder_int in HfinalInv; cbn in HfinalInv; tauto).
  have HentryFrame : writeSuccessMemoryRangeFrame (bv_unsigned sp - 16) 16
      finalGlobal.(seq_mem) outputGlobal.(seq_mem) by
    (unfold Inv_encoder_int in HfinalInv; cbn in HfinalInv; tauto).
  destruct (writeSuccessEncoderIntCaller156dc finalGlobal Htable) as
    (Halign & trace & Hcode).
  have Hpc := writeSuccessWithdrawalsEncoderIntEndpointPc finalRegs finalGlobal
    sp (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal)
    trace Halign Hcode.
  have HglobalEnd := writeSuccessWithdrawalsEncoderIntEndpointGlobal finalRegs
    finalGlobal sp (Z_to_bv 64 0x156dc)
    (writeSuccessWithdrawalsAmountValue withdrawal) trace Halign Hcode.
  have HfactsEnd := writeSuccessEncoderIntEndpointFacts finalRegs sp
    (Z_to_bv 64 0x156dc) Hfacts.
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
  have HframeEnd := writeSuccessEncoderIntGlobal2Frame finalGlobal
    outputGlobal.(seq_mem) sp (Z_to_bv 64 0x156dc)
    (writeSuccessWithdrawalsAmountValue withdrawal) Hrange Hbacked HentryFrame.
  have HouterOutput := writeSuccessFinalOutputMemoryFrame args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 outputRegs outputGlobal Hinv Hprefix Hentry1 Hentry2
    Houtput.
  have HfinalGlobal := f_equal snd HfinalEntry. cbn in HfinalGlobal.
  have HouterFinal : writeSuccessWithdrawalsMemoryFrame sp
      finalGlobal.(seq_mem) memoryFrame by
    (rewrite <- HfinalGlobal; exact HouterOutput).
  have HframeFinal : writeSuccessMemoryRangeFrame (bv_unsigned sp - 16) 16
      (writeSuccessEncoderIntGlobal2 finalGlobal sp (Z_to_bv 64 0x156dc)
        (writeSuccessWithdrawalsAmountValue withdrawal)).(seq_mem)
      finalGlobal.(seq_mem).
  { rewrite HfinalGlobal in HframeEnd. exact HframeEnd. }
  have HouterEnd := writeSuccessWithdrawalsMemoryFrameLowScratch sp
    finalGlobal.(seq_mem)
    (writeSuccessEncoderIntGlobal2 finalGlobal sp (Z_to_bv 64 0x156dc)
      (writeSuccessWithdrawalsAmountValue withdrawal)).(seq_mem)
    memoryFrame HouterFinal HframeFinal.
  repeat split.
  - exact Hpc.
  - rewrite (writeSuccessWithdrawalsEncoderIntEndpointLookupOther finalRegs
      finalGlobal sp (Z_to_bv 64 0x156dc)
      (writeSuccessWithdrawalsAmountValue withdrawal) trace "x8" Halign Hcode);
      try discriminate. exact Hfinal8.
  - rewrite (writeSuccessWithdrawalsEncoderIntEndpointLookupOther finalRegs
      finalGlobal sp (Z_to_bv 64 0x156dc)
      (writeSuccessWithdrawalsAmountValue withdrawal) trace "x9" Halign Hcode);
      try discriminate. exact Hfinal9.
  - rewrite (writeSuccessWithdrawalsEncoderIntEndpointLookupOther finalRegs
      finalGlobal sp (Z_to_bv 64 0x156dc)
      (writeSuccessWithdrawalsAmountValue withdrawal) trace "x18" Halign Hcode);
      try discriminate. exact Hfinal18.
  - rewrite HregsEnd. exact (proj1 HfactsEnd).
  - rewrite HglobalEnd. unfold writeSuccessWithdrawalsInstructionTable in
      Htable |- *. intros pc instruction Hinstruction. apply Htable.
    exact Hinstruction.
  - rewrite HglobalEnd. exact (proj1 HframeEnd).
  - rewrite HglobalEnd. exact (proj2 HframeEnd).
  - rewrite HglobalEnd. exact (proj1 HouterEnd).
  - rewrite HglobalEnd. exact (proj2 HouterEnd).
  - exact HglobalEnd.
Qed.

Print Assumptions writeSuccessWithdrawalsSecondEncoderEndpointIterationRegisters.
Print Assumptions writeSuccessWithdrawalsFinalEncoderEndpointPackage.
