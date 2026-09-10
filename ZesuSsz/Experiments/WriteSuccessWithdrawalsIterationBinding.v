From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationOff.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalEndpointMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalAmountRead.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationBindingContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationBounds.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIteration410.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpyState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsTailEndpointPackage.

Open Scope Z_scope.

Lemma block_15694_iteration : block_15694_iteration_statement.
Proof.
  unfold block_15694_iteration_statement.
  intros args sp pointer base total processed r withdrawal nextWithdrawal
    allBytes prefix current nextCurrent nextSuffix scratch encoderScratch
    registerFrame memoryFrame priorLog state Hinv Hnext HnextLength.
  destruct (writeSuccessWithdrawalsNonfinalIterationContext args sp pointer
    base total processed r withdrawal nextWithdrawal allBytes prefix current
    nextCurrent nextSuffix scratch encoderScratch registerFrame memoryFrame
    priorLog state Hinv Hnext HnextLength) as
    (segments & after & records & padding & nextPadding & regs0 & global0 &
     regs1 & global1 & regs2 & global2 & outputRegs & outputGlobal & finalRegs &
     finalGlobal & Hrecorded & Hafter & Hlog & Hrecords & Hpadding & Hcurrent &
     Hpointer & Hall & HprefixLength & Hdrop & HsuffixLength & HnextPadding &
     HnextShape & Hprefix & Hentry1 & Hentry2 & Houtput & HfinalEntry).
  subst after.
  destruct Hrecorded as (Hrun & _).
  have Htail := writeSuccessWithdrawalsFinalEncoderTailEndpointPackage args sp
    pointer base total processed (S r) withdrawal allBytes prefix current
    (nextCurrent ++ nextSuffix) scratch encoderScratch registerFrame memoryFrame
    priorLog state regs0 global0 regs1 global1 regs2 global2 outputRegs
    outputGlobal finalRegs finalGlobal Hinv Hprefix Hentry1 Hentry2 Houtput
    HfinalEntry.
  cbn in Htail.
  destruct Htail as (Hboundary & HpcRegister & Hpc & Hx2 & Hx8 & Hx9 & Hx18 &
    Hfacts & HregisterFrame & HmemoryFrame & Hhigh & Hlow & Hmmio & Htable &
    Hglobal).
  have HspUpper : bv_unsigned sp + 1792 < 0x40000000 by
    (pose proof Hinv as HinvSpUpper; unfold Inv_15694 in HinvSpUpper; tauto).
  have HdestinationUnsigned :=
    writeSuccessWithdrawalsPrefixDestinationUnsigned sp HspUpper.
  have HhighLinear : read_mem_list
      (writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal sp
        pointer (S r) withdrawal).2.(seq_mem)
      (bv_unsigned sp + 1744) 48%N = Some current by
    (rewrite <- HdestinationUnsigned; exact Hhigh).
  have HendpointMemory := writeSuccessWithdrawalsFinalEndpointMemory args sp
    pointer base total processed (S r) withdrawal allBytes prefix current
    (nextCurrent ++ nextSuffix) scratch encoderScratch registerFrame memoryFrame
    priorLog state regs0 global0 regs1 global1 regs2 global2 outputRegs
    outputGlobal finalRegs finalGlobal Hinv Hprefix Hentry1 Hentry2 Houtput
    HfinalEntry.
  cbn in HendpointMemory.
  destruct HendpointMemory as (_ & HallReadEndpoint & HitemsEndpoint &
    HrepresentationEndpoint & _).
  have HnextReadEndpoint :=
    writeSuccessWithdrawalsFinalEndpointNextCurrentRead args sp pointer base
      total processed r withdrawal nextWithdrawal allBytes prefix current
      nextCurrent nextSuffix scratch encoderScratch registerFrame memoryFrame
      priorLog state regs0 global0 regs1 global1 regs2 global2 outputRegs
      outputGlobal finalRegs finalGlobal Hinv Hnext HnextLength Hprefix Hentry1
      Hentry2 Houtput HfinalEntry.
  have HallRead : read_mem_list
      (writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal sp
        pointer (S r) withdrawal).2.(seq_mem) base
      (N.of_nat (length allBytes)) = Some allBytes by
    (rewrite Hglobal; exact HallReadEndpoint).
  have Hitems : writeSuccessWithdrawalItemsAt
      (writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal sp
        pointer (S r) withdrawal).2.(seq_mem) base
      (observationWithdrawals (successDecoded WriteSuccessObservation args)) by
    (rewrite Hglobal; exact HitemsEndpoint).
  have Hrepresentation : writeSuccessConcreteRepresentationOff
      (successStackPointer WriteSuccessObservation args)
      (successDecoded WriteSuccessObservation args)
      (writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal sp
        pointer (S r) withdrawal).2.(seq_mem)
      (successDecodedAddress WriteSuccessObservation args) by
    (rewrite Hglobal; exact HrepresentationEndpoint).
  have HnextRead : read_mem_list
      (writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal sp
        pointer (S r) withdrawal).2.(seq_mem)
      (bv_unsigned (pointer + BV 64 48)%bv) 48%N = Some nextCurrent by
    (rewrite Hglobal; exact HnextReadEndpoint).
  have HnextMemory : writeSuccessWithdrawalMemory
      (writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal sp
        pointer (S r) withdrawal).2.(seq_mem)
      (bv_unsigned (pointer + BV 64 48)%bv) nextWithdrawal.
  { unfold writeSuccessWithdrawalItemsAt in Hitems.
    rewrite Hpointer. exact (Hitems (S processed) nextWithdrawal Hnext). }
  have HtotalLength : total = length (observationWithdrawals
      (successDecoded WriteSuccessObservation args)) by
    (pose proof Hinv as HinvTotalLength;
     unfold Inv_15694 in HinvTotalLength; tauto).
  have Htotal0 : total = (processed + S (S r))%nat.
  { pose proof Hinv as HinvTotal.
    unfold Inv_15694 in HinvTotal. tauto. }
  have Htotal : total = (S processed + S r)%nat by lia.
  have HbaseHigh : islaMemoryRangesDisjoint base (length allBytes)
      (bv_unsigned sp + 1744) 48 by
    (pose proof Hinv as HinvBaseHigh;
     unfold Inv_15694 in HinvBaseHigh; tauto).
  have HnextLower : base <= bv_unsigned (pointer + BV 64 48)%bv by
    (rewrite Hpointer; pose proof (Nat2Z.is_nonneg (S processed)); lia).
  have HnextUpper : bv_unsigned (pointer + BV 64 48)%bv + 48 <=
      base + Z.of_nat (length allBytes).
  { rewrite Hpointer.
    have Hlength : length allBytes =
        (length (prefix ++ current) + length nextCurrent +
          length nextSuffix)%nat by
      (rewrite Hall; repeat rewrite app_length; lia).
    rewrite HprefixLength HnextLength HsuffixLength in Hlength.
    have HlengthZ := f_equal Z.of_nat Hlength.
    rewrite !Nat2Z.inj_add in HlengthZ. cbn in HlengthZ. lia. }
  have HnextDisjoint : islaMemoryRangesDisjoint
      (bv_unsigned (pointer + BV 64 48)%bv) 48
      (bv_unsigned sp + 1744) 48.
  { unfold islaMemoryRangesDisjoint in HbaseHigh |- *.
    destruct HbaseHigh; [left|right]; lia. }
  destruct (proj2 (proj2 Hfacts) "x1" ltac:(cbn; tauto)) as (oldX1 & Hx1).
  destruct (proj2 (proj2 Hfacts) "x10" ltac:(cbn; tauto)) as (oldX10 & Hx10).
  destruct (proj2 (proj2 Hfacts) "x11" ltac:(cbn; tauto)) as (oldX11 & Hx11).
  destruct (proj2 (proj2 Hfacts) "x12" ltac:(cbn; tauto)) as (oldX12 & Hx12).
  destruct (proj2 (proj2 Hfacts) "x15" ltac:(cbn; tauto)) as (oldX15 & Hx15).
  exists segments,
    (writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal sp
       pointer (S r) withdrawal,
     writeSuccessWithdrawalsIteration410Log priorLog global1 global2
       outputGlobal finalGlobal sp withdrawal), records, padding,
    (bv_to_little_endian 8 8
       (bv_unsigned (writeSuccessWithdrawalsAmountValue withdrawal)) ++
     bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 0x156dc))).
  split; first exact Hrun.
  split; first exact Hlog.
  split; first exact Hrecords.
  split; first exact Hpadding.
  split; first exact Hcurrent.
  split; first exact HhighLinear.
  unfold Inv_15694.
  unfold Inv_15694 in Hinv.
  split; first exact Hboundary.
  split; first exact HpcRegister.
  split; first (cbn in Hpc; exact Hpc).
  split; first (exists (RVal_Bits oldX1); exact Hx1).
  split; first exact Hx2.
  split; first (exists (RVal_Bits oldX10); exact Hx10).
  split; first (exists (RVal_Bits oldX11); exact Hx11).
  split; first (exists (RVal_Bits oldX12); exact Hx12).
  split; first (exists (RVal_Bits oldX15); exact Hx15).
  split; first exact Hx8.
  split; first exact Hx9.
  split; first exact Hx18.
  split; first exact HregisterFrame.
  split; first exact HmemoryFrame.
  split; first exact Htable.
  split; first exact Hfacts.
  split; first exact Hrepresentation.
  split; first exact Hitems.
  split; first exact HtotalLength.
  split; first exact Htotal.
  split; first exact Hnext.
  split; first exact Hall.
  split; first exact HprefixLength.
  split; first exact HnextLength.
  split; first (cbn; exact HsuffixLength).
  split; first tauto.
  split; first tauto.
  split; first tauto.
  split; first tauto.
  split; first tauto.
  split; first tauto.
  split; first exact Hpointer.
  split; first exact HallRead.
  split; first exact HnextRead.
  split; first exact HnextMemory.
  split; first exact HhighLinear.
  split; first exact Hlow.
  split; first exact HnextDisjoint.
  split; first tauto.
  split; first exact HbaseHigh.
  split; first exact Hmmio.
  exact Hlog.
Qed.

Lemma block_15694_last_iteration : block_15694_last_iteration_statement.
Proof.
  unfold block_15694_last_iteration_statement.
  intros args sp pointer base total processed withdrawal allBytes prefix current
    scratch encoderScratch registerFrame memoryFrame priorLog state Hinv.
  destruct (writeSuccessWithdrawalsLastIterationContext args sp pointer base
    total processed withdrawal allBytes prefix current scratch encoderScratch
    registerFrame memoryFrame priorLog state Hinv) as
    (segments & after & records & padding & regs0 & global0 & regs1 & global1 &
     regs2 & global2 & outputRegs & outputGlobal & finalRegs & finalGlobal &
     Hrecorded & Hafter & Hlog & Hrecords & Hpadding & Hcurrent & Hall &
     Hlength & Hpointer & Hprefix & Hentry1 & Hentry2 & Houtput & HfinalEntry).
  subst after. destruct Hrecorded as (Hrun & _).
  have Htail := writeSuccessWithdrawalsFinalEncoderTailEndpointPackage args sp
    pointer base total processed 0 withdrawal allBytes prefix current [] scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 outputRegs outputGlobal finalRegs finalGlobal Hinv
    Hprefix Hentry1 Hentry2 Houtput HfinalEntry.
  cbn in Htail.
  destruct Htail as (Hboundary & HpcRegister & Hpc & Hx2 & Hx8 & Hx9 & Hx18 &
    Hfacts & HregisterFrame & HmemoryFrame & Hhigh & Hlow & Hmmio & Htable &
    Hglobal).
  have HspUpper : bv_unsigned sp + 1792 < 0x40000000 by
    (pose proof Hinv as HinvSpUpper; unfold Inv_15694 in HinvSpUpper; tauto).
  have HdestinationUnsigned :=
    writeSuccessWithdrawalsPrefixDestinationUnsigned sp HspUpper.
  have HhighLinear : read_mem_list
      (writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal sp
        pointer 0 withdrawal).2.(seq_mem)
      (bv_unsigned sp + 1744) 48%N = Some current by
    (rewrite <- HdestinationUnsigned; exact Hhigh).
  have HendpointMemory := writeSuccessWithdrawalsFinalEndpointMemory args sp
    pointer base total processed 0 withdrawal allBytes prefix current [] scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 outputRegs outputGlobal finalRegs finalGlobal Hinv
    Hprefix Hentry1 Hentry2 Houtput HfinalEntry.
  cbn in HendpointMemory.
  destruct HendpointMemory as (_ & HallReadEndpoint & HitemsEndpoint &
    HrepresentationEndpoint & _).
  have HallRead : read_mem_list
      (writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal sp
        pointer 0 withdrawal).2.(seq_mem) base
      (N.of_nat (length allBytes)) = Some allBytes by
    (rewrite Hglobal; exact HallReadEndpoint).
  have Hitems : writeSuccessWithdrawalItemsAt
      (writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal sp
        pointer 0 withdrawal).2.(seq_mem) base
      (observationWithdrawals (successDecoded WriteSuccessObservation args)) by
    (rewrite Hglobal; exact HitemsEndpoint).
  have Hrepresentation : writeSuccessConcreteRepresentationOff
      (successStackPointer WriteSuccessObservation args)
      (successDecoded WriteSuccessObservation args)
      (writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal sp
        pointer 0 withdrawal).2.(seq_mem)
      (successDecodedAddress WriteSuccessObservation args) by
    (rewrite Hglobal; exact HrepresentationEndpoint).
  exists segments,
    (writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal sp
       pointer 0 withdrawal,
     writeSuccessWithdrawalsIteration410Log priorLog global1 global2
       outputGlobal finalGlobal sp withdrawal), records, padding.
  split; first exact Hrun.
  split; first exact Hlog.
  split; first exact Hrecords.
  split; first exact Hpadding.
  split; first exact Hcurrent.
  split; first exact HhighLinear.
  unfold Inv_156e8.
  split; first exact Hboundary.
  split; first exact HpcRegister.
  split; first (cbn in Hpc; exact Hpc).
  split; first exact Hx2.
  split; first exact Hx8.
  split.
  { replace (Z_to_bv 64 0%nat) with (BV 64 0) in Hx9 by bv_solve.
    exact Hx9. }
  split; first exact Hpointer.
  split; first exact HregisterFrame.
  split; first exact HmemoryFrame.
  split; first exact Htable.
  split; first exact Hfacts.
  split; first exact Hrepresentation.
  split; first exact Hitems.
  split; first exact HallRead.
  exact Hlog.
Qed.

Print Assumptions block_15694_iteration.
Print Assumptions block_15694_last_iteration.
