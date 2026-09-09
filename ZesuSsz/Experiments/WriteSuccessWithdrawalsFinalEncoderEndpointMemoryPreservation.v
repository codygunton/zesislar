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
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOutputEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalEncoderEndpointFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalAddressRead.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntScratch.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntMemory.
Open Scope Z_scope.

Lemma writeSuccessWithdrawalsFinalEncoderEndpointMemoryPreservation args sp pointer
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
  read_mem_list endpoint.2.(seq_mem)
      (bv_unsigned (sp + BV 64 1744)%bv) 48%N = Some current /\
  read_mem_list endpoint.2.(seq_mem) (bv_unsigned sp - 16) 16%N =
    Some
      (bv_to_little_endian 8 8
         (bv_unsigned (writeSuccessWithdrawalsAmountValue withdrawal)) ++
       bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 0x156dc))) /\
  set_Forall
    (fun address =>
      ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
    (dom endpoint.2.(seq_mem)).
Proof.
  intros Hinv Hp He1 He2 Ho Hfinal. cbn.
  have Hpackage := writeSuccessWithdrawalsFinalEncoderEndpointPackage args sp
    pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 regs2 global2 outputRegs outputGlobal finalRegs
    finalGlobal Hinv Hp He1 He2 Ho Hfinal.
  cbn in Hpackage.
  destruct Hpackage as (_ & _ & _ & _ & _ & _ & _ & HouterFrame &
    HglobalEnd).
  have Hrange : islaMemoryRange (bv_unsigned sp - 16) 16.
  { unfold Inv_15694 in Hinv. unfold islaMemoryRange.
    pose proof (bv_unsigned_in_range 64 sp). lia. }
  have Hhigh0 := writeSuccessWithdrawals156a8DestinationRead args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 Hinv.
  have Hupper : bv_unsigned sp + 1792 < 0x40000000 by
    (unfold Inv_15694 in Hinv; tauto).
  have HhighAddress : bv_unsigned (sp + BV 64 1744)%bv =
      bv_unsigned sp + 1744 by
    (apply writeSuccessWithdrawalsPrefixDestinationUnsigned; exact Hupper).
  have Hdisjoint : islaMemoryRangesDisjoint (bv_unsigned sp - 16) 16
      (bv_unsigned (sp + BV 64 1744)%bv) 48.
  { unfold islaMemoryRangesDisjoint. rewrite HhighAddress. lia. }
  have Hhigh1 := writeSuccessEncoderIntGlobal2ReadListDisjoint
    (writeSuccessWithdrawals156a8Global regs0 global0 sp pointer current) sp
    (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)
    (bv_unsigned (sp + BV 64 1744)%bv) 48 current Hrange Hdisjoint Hhigh0.
  have Hhigh2 := writeSuccessEncoderIntGlobal2ReadListDisjoint
    (writeSuccessEncoderIntGlobal2
      (writeSuccessWithdrawals156a8Global regs0 global0 sp pointer current) sp
      (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)) sp
    (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal)
    (bv_unsigned (sp + BV 64 1744)%bv) 48 current Hrange Hdisjoint Hhigh1.
  have Hhigh3 := writeSuccessEncoderIntGlobal2ReadListDisjoint
    (writeSuccessEncoderIntGlobal2
      (writeSuccessEncoderIntGlobal2
        (writeSuccessWithdrawals156a8Global regs0 global0 sp pointer current) sp
        (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)) sp
      (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal)) sp
    (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal)
    (bv_unsigned (sp + BV 64 1744)%bv) 48 current Hrange Hdisjoint Hhigh2.
  have Hglobal := writeSuccessFinalAddressOutputGlobal args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 regs2 global2 outputRegs outputGlobal Hinv Hp He1 He2
    Ho.
  have HfinalGlobal := f_equal snd Hfinal. cbn in HfinalGlobal.
  have HendpointGlobal :
      (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
        (Z_to_bv 64 0x156dc)
        (writeSuccessWithdrawalsAmountValue withdrawal)).2 =
      writeSuccessEncoderIntGlobal2
        (writeSuccessEncoderIntGlobal2
          (writeSuccessEncoderIntGlobal2
            (writeSuccessWithdrawals156a8Global regs0 global0 sp pointer
              current) sp (Z_to_bv 64 0x156b4)
            (writeSuccessWithdrawalsIndexValue withdrawal)) sp
          (Z_to_bv 64 0x156c0)
          (writeSuccessWithdrawalsValidatorValue withdrawal)) sp
        (Z_to_bv 64 0x156dc)
        (writeSuccessWithdrawalsAmountValue withdrawal).
  { rewrite HglobalEnd. rewrite <- HfinalGlobal. rewrite Hglobal. reflexivity. }
  have HhighEnd : read_mem_list
      (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
        (Z_to_bv 64 0x156dc)
        (writeSuccessWithdrawalsAmountValue withdrawal)).2.(seq_mem)
      (bv_unsigned (sp + BV 64 1744)%bv) 48%N = Some current by
    (rewrite HendpointGlobal; exact Hhigh3).
  have HscratchEnd : read_mem_list
      (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
        (Z_to_bv 64 0x156dc)
        (writeSuccessWithdrawalsAmountValue withdrawal)).2.(seq_mem)
      (bv_unsigned sp - 16) 16%N =
    Some
      (bv_to_little_endian 8 8
         (bv_unsigned (writeSuccessWithdrawalsAmountValue withdrawal)) ++
       bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 0x156dc))).
  { rewrite HglobalEnd. apply writeSuccessEncoderIntAfterStoresScratch.
    exact Hrange. }
  have Hmmio0 : set_Forall
      (fun address =>
        ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
      (dom state.1.2.(seq_mem)) by (unfold Inv_15694 in Hinv; tauto).
  have HentryMemoryFrame : writeSuccessWithdrawalsMemoryFrame sp
      state.1.2.(seq_mem) memoryFrame by (unfold Inv_15694 in Hinv; tauto).
  have HmmioEnd : set_Forall
      (fun address =>
        ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
      (dom (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
        (Z_to_bv 64 0x156dc)
        (writeSuccessWithdrawalsAmountValue withdrawal)).2.(seq_mem)).
  { destruct HentryMemoryFrame as [Hdom0 _].
    destruct HouterFrame as [HdomEnd _].
    rewrite HdomEnd. rewrite <- Hdom0. exact Hmmio0. }
  repeat split; assumption.
Qed.

Print Assumptions writeSuccessWithdrawalsFinalEncoderEndpointMemoryPreservation.
