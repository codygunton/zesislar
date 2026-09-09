From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationOff.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationOffPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationOffValid.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalEncoderEndpointFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalAmountRead.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsItemsPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationSemantic.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOutputEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsFinalEndpointMemory args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 outputRegs outputGlobal finalRegs finalGlobal :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
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
  writeSuccessWithdrawalsMemoryFrame sp endpoint.2.(seq_mem) memoryFrame /\
  read_mem_list endpoint.2.(seq_mem) base
    (N.of_nat (length allBytes)) = Some allBytes /\
  writeSuccessWithdrawalItemsAt endpoint.2.(seq_mem) base
    (observationWithdrawals (successDecoded WriteSuccessObservation args)) /\
  writeSuccessConcreteRepresentationOff
    (successStackPointer WriteSuccessObservation args)
    (successDecoded WriteSuccessObservation args) endpoint.2.(seq_mem)
    (successDecodedAddress WriteSuccessObservation args) /\
  set_Forall
    (fun address =>
      ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
    (dom endpoint.2.(seq_mem)).
Proof.
  intros Hinv Hprefix Hentry1 Hentry2 Houtput HfinalEntry. cbn.
  destruct (writeSuccessWithdrawalsFinalEncoderEndpointPackage args sp pointer
    base total processed (S remaining) withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 regs2 global2 outputRegs outputGlobal finalRegs
    finalGlobal Hinv Hprefix Hentry1 Hentry2 Houtput HfinalEntry) as
    (_ & _ & _ & _ & _ & _ & _ & HafterFrame & _).
  have HbeforeFrame : writeSuccessWithdrawalsMemoryFrame sp
      state.1.2.(seq_mem) memoryFrame by
    (unfold Inv_15694 in Hinv; tauto).
  have Hsp : bv_unsigned sp =
      successStackPointer WriteSuccessObservation args - 2000 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hrepresentation : writeSuccessConcreteRepresentationOff
      (successStackPointer WriteSuccessObservation args)
      (successDecoded WriteSuccessObservation args) state.1.2.(seq_mem)
      (successDecodedAddress WriteSuccessObservation args) by
    (unfold Inv_15694 in Hinv; tauto).
  have Hitems : writeSuccessWithdrawalItemsAt state.1.2.(seq_mem) base
      (observationWithdrawals (successDecoded WriteSuccessObservation args)) by
    (unfold Inv_15694 in Hinv; tauto).
  have Htotal : total = length (observationWithdrawals
      (successDecoded WriteSuccessObservation args)) by
    (unfold Inv_15694 in Hinv; tauto).
  have HallRead : read_mem_list state.1.2.(seq_mem) base
      (N.of_nat (length allBytes)) = Some allBytes by
    (unfold Inv_15694 in Hinv; tauto).
  have Hlow : islaMemoryRangesDisjoint base (length allBytes)
      (bv_unsigned sp - 16) 16 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hhigh : islaMemoryRangesDisjoint base (length allBytes)
      (bv_unsigned sp + 1744) 48 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hmmio : set_Forall
      (fun address =>
        ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
      (dom state.1.2.(seq_mem)) by
    (unfold Inv_15694 in Hinv; tauto).
  have HallLength : length allBytes = (48 * total)%nat.
  { have Hall : allBytes = prefix ++ current ++ suffix by
      (unfold Inv_15694 in Hinv; tauto).
    have HprefixLength : length prefix = (48 * processed)%nat by
      (unfold Inv_15694 in Hinv; tauto).
    have HcurrentLength : length current = 48%nat by
      (unfold Inv_15694 in Hinv; tauto).
    have HsuffixLength : length suffix = (48 * remaining)%nat by
      (unfold Inv_15694 in Hinv; cbn in Hinv; tauto).
    have Hremaining : total = (processed + S remaining)%nat by
      (unfold Inv_15694 in Hinv; tauto).
    rewrite Hall !app_length HprefixLength HcurrentLength HsuffixLength
      Hremaining. lia. }
  have HvalidObservation := writeSuccessConcreteRepresentationOffValid _ _ _ _
    Hrepresentation.
  have HvalidItems : Forall writeSuccessWithdrawalObservationValid
      (observationWithdrawals (successDecoded WriteSuccessObservation args)) by
    (unfold writeSuccessObservationValid, writeSuccessListValid in
      HvalidObservation; tauto).
  have HitemsAfter := writeSuccessWithdrawalItemsAtWithdrawalsFrames sp
    state.1.2.(seq_mem)
    (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
      (Z_to_bv 64 0x156dc)
      (writeSuccessWithdrawalsAmountValue withdrawal)).2.(seq_mem)
    memoryFrame base
    (observationWithdrawals (successDecoded WriteSuccessObservation args))
    HbeforeFrame HafterFrame.
  specialize (HitemsAfter ltac:(rewrite <- Htotal, <- HallLength; exact Hlow)
    ltac:(rewrite <- Htotal, <- HallLength; exact Hhigh) HvalidItems Hitems).
  have HallReadAfter : read_mem_list
      (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
        (Z_to_bv 64 0x156dc)
        (writeSuccessWithdrawalsAmountValue withdrawal)).2.(seq_mem)
      base (N.of_nat (length allBytes)) = Some allBytes.
  { rewrite (writeSuccessReadMemListWithinWithdrawalsFrames sp
      state.1.2.(seq_mem)
      (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
        (Z_to_bv 64 0x156dc)
        (writeSuccessWithdrawalsAmountValue withdrawal)).2.(seq_mem)
      memoryFrame base (length allBytes) base (length allBytes)
      HbeforeFrame HafterFrame Hlow Hhigh ltac:(lia) ltac:(lia)).
    exact HallRead. }
  have HrepresentationAfter :=
    writeSuccessConcreteRepresentationOffWithdrawalsFrames
      (successStackPointer WriteSuccessObservation args) sp
      (successDecoded WriteSuccessObservation args) state.1.2.(seq_mem)
      (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
        (Z_to_bv 64 0x156dc)
        (writeSuccessWithdrawalsAmountValue withdrawal)).2.(seq_mem)
      memoryFrame (successDecodedAddress WriteSuccessObservation args)
      Hsp Hrepresentation HbeforeFrame HafterFrame.
  have Hdom : dom
      (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
        (Z_to_bv 64 0x156dc)
        (writeSuccessWithdrawalsAmountValue withdrawal)).2.(seq_mem) =
      dom state.1.2.(seq_mem).
  { destruct HbeforeFrame as [HbeforeDom _].
    destruct HafterFrame as [HafterDom _]. congruence. }
  split; first exact HafterFrame.
  split; first exact HallReadAfter.
  split; first exact HitemsAfter.
  split; first exact HrepresentationAfter.
  rewrite Hdom. exact Hmmio.
Qed.

Lemma writeSuccessWithdrawalsFinalEndpointNextCurrentRead args sp pointer base
    total processed r withdrawal nextWithdrawal allBytes prefix current
    nextCurrent nextSuffix scratch encoderScratch registerFrame memoryFrame
    priorLog state regs0 global0 regs1 global1 regs2 global2 outputRegs
    outputGlobal finalRegs finalGlobal :
  Inv_15694 args sp pointer base total processed (S (S r)) withdrawal
    allBytes prefix current (nextCurrent ++ nextSuffix) scratch encoderScratch
    registerFrame memoryFrame priorLog state ->
  nth_error (observationWithdrawals
    (successDecoded WriteSuccessObservation args)) (S processed) =
    Some nextWithdrawal ->
  length nextCurrent = 48%nat ->
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
  read_mem_list
    (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
      (Z_to_bv 64 0x156dc)
      (writeSuccessWithdrawalsAmountValue withdrawal)).2.(seq_mem)
    (bv_unsigned (pointer + BV 64 48)%bv) 48%N = Some nextCurrent.
Proof.
  intros Hinv Hnext HnextLength Hprefix Hentry1 Hentry2 Houtput HfinalEntry.
  destruct (writeSuccessWithdrawalsFinalEncoderEndpointPackage args sp pointer
    base total processed (S (S r)) withdrawal allBytes prefix current
    (nextCurrent ++ nextSuffix) scratch encoderScratch registerFrame memoryFrame
    priorLog state regs0 global0 regs1 global1 regs2 global2 outputRegs
    outputGlobal finalRegs finalGlobal Hinv Hprefix Hentry1 Hentry2 Houtput
    HfinalEntry) as (_ & _ & _ & _ & _ & _ & _ & HafterFrame & _).
  have HbeforeFrame : writeSuccessWithdrawalsMemoryFrame sp
      state.1.2.(seq_mem) memoryFrame by
    (unfold Inv_15694 in Hinv; tauto).
  have Hlow : islaMemoryRangesDisjoint base (length allBytes)
      (bv_unsigned sp - 16) 16 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hhigh : islaMemoryRangesDisjoint base (length allBytes)
      (bv_unsigned sp + 1744) 48 by
    (unfold Inv_15694 in Hinv; tauto).
  destruct (writeSuccessWithdrawalsNonfinalSemanticTransition args sp pointer
    base total processed r withdrawal nextWithdrawal allBytes prefix current
    nextCurrent nextSuffix scratch encoderScratch registerFrame memoryFrame
    priorLog state Hinv Hnext HnextLength) as
    (padding & nextPadding & Hpadding & Hcurrent & HpointerNext & Hall &
      HprefixLength & Hdrop & HnextSuffixLength & HnextPadding & HnextShape &
      HsourceRead & HnextMemory).
  have HaddressLower : base <= bv_unsigned (pointer + BV 64 48)%bv by
    (rewrite HpointerNext; pose proof (Nat2Z.is_nonneg (S processed)); lia).
  have HaddressUpper :
      bv_unsigned (pointer + BV 64 48)%bv + Z.of_nat 48 <=
      base + Z.of_nat (length allBytes).
  { rewrite HpointerNext.
    have HallLengthNat : length allBytes =
        (length (prefix ++ current) + length nextCurrent +
          length nextSuffix)%nat.
    { rewrite Hall.
      rewrite (app_length (prefix ++ current) (nextCurrent ++ nextSuffix)).
      rewrite (app_length nextCurrent nextSuffix). lia. }
    rewrite HprefixLength HnextLength in HallLengthNat.
    have HallLength := f_equal Z.of_nat HallLengthNat.
    rewrite !Nat2Z.inj_add in HallLength. cbn in HallLength. lia. }
  rewrite (writeSuccessReadMemListWithinWithdrawalsFrames sp
    state.1.2.(seq_mem)
    (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
      (Z_to_bv 64 0x156dc)
      (writeSuccessWithdrawalsAmountValue withdrawal)).2.(seq_mem)
    memoryFrame base (length allBytes)
    (bv_unsigned (pointer + BV 64 48)%bv) 48 HbeforeFrame HafterFrame Hlow
    Hhigh HaddressLower HaddressUpper).
  exact HsourceRead.
Qed.

Print Assumptions writeSuccessWithdrawalsFinalEndpointMemory.
Print Assumptions writeSuccessWithdrawalsFinalEndpointNextCurrentRead.
