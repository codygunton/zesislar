From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessBlockFramework.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101dc.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyAfter.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyBoundaryFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyEntry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyInduction.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyReadiness.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.

Import ListNotations.
Open Scope Z_scope.

Local Opaque writeSuccessMemoryRangeFrame.

Theorem block_memcpy : block_memcpy_statement.
Proof.
  unfold block_memcpy_statement.
  intros destination source returnAddress bytes destinationBefore memoryFrame
    priorLog state Hinv.
  destruct state as [machine log].
  destruct (writeSuccessMemcpyEntryShape destination source returnAddress bytes
    destinationBefore memoryFrame priorLog (machine, log) Hinv) as
    (regs & global & Hmachine).
  cbn in Hmachine. subst machine.
  have Hboundary : IslaInstructionBoundary (writeSuccess101d4Before regs global) by
    (unfold Inv_memcpy in Hinv; cbn in Hinv; tauto).
  have HconcretePc :
      match regs !! "PC" with
      | Some (RVal_Bits value) => Some (bvn_unsigned value)
      | _ => None
      end = Some 0x101d4 by
    (unfold Inv_memcpy, writeSuccessWithdrawalsConcretePc in Hinv;
      cbn in Hinv; tauto).
  destruct Hboundary as (_ & pc & entryTrace & Hpc & _).
  cbn in Hpc. rewrite Hpc in HconcretePc.
  inversion HconcretePc as [Hunsigned].
  change (bv_unsigned pc = 0x101d4) in Hunsigned.
  have Hpceq : pc = Z_to_bv 64 0x101d4.
  { rewrite <- (Z_to_bv_bv_unsigned 64 pc), Hunsigned. reflexivity. }
  subst pc.
  have Hx1 : regs !! "x1" = Some (RVal_Bits returnAddress) by
    (unfold Inv_memcpy in Hinv; cbn in Hinv; tauto).
  have Hx10 : regs !! "x10" = Some (RVal_Bits destination) by
    (unfold Inv_memcpy in Hinv; cbn in Hinv; tauto).
  have Hx11 : regs !! "x11" = Some (RVal_Bits source) by
    (unfold Inv_memcpy in Hinv; cbn in Hinv; tauto).
  have Hx12 : regs !! "x12" = Some
      (RVal_Bits (Z_to_bv 64 (Z.of_nat (length bytes)))) by
    (unfold Inv_memcpy in Hinv; cbn in Hinv; tauto).
  have Halign : bv_extract 0 2 returnAddress = BV 2 0 by
    (unfold Inv_memcpy in Hinv; cbn in Hinv; tauto).
  have Hreturn : exists returnTrace,
      global.(seq_instrs) !! returnAddress = Some returnTrace by
    (unfold Inv_memcpy in Hinv; cbn in Hinv; tauto).
  have Htable : writeSuccessWithdrawalsInstructionTable global by
    (unfold Inv_memcpy in Hinv; cbn in Hinv; tauto).
  have Hfacts : writeSuccessWithdrawalsOperationalRegisterFacts regs by
    (unfold Inv_memcpy in Hinv; cbn in Hinv; tauto).
  have Hsource : read_mem_list global.(seq_mem) (bv_unsigned source)
      (N.of_nat (length bytes)) = Some bytes by
    (unfold Inv_memcpy in Hinv; cbn in Hinv; tauto).
  have Hrange : islaMemoryRange (bv_unsigned destination) (length bytes) by
    (unfold Inv_memcpy in Hinv; cbn in Hinv; tauto).
  have HsourceLower : 0x20000000 <= bv_unsigned source by
    (unfold Inv_memcpy in Hinv; cbn in Hinv; tauto).
  have HsourceUpper : bv_unsigned source + Z.of_nat (length bytes) <=
      0x40000000 by (unfold Inv_memcpy in Hinv; cbn in Hinv; tauto).
  have HdestinationLower : 0x20000000 <= bv_unsigned destination by
    (unfold Inv_memcpy in Hinv; cbn in Hinv; tauto).
  have HdestinationUpper : bv_unsigned destination + Z.of_nat (length bytes) <=
      0x40000000 by (unfold Inv_memcpy in Hinv; cbn in Hinv; tauto).
  have Hdisjoint : islaMemoryRangesDisjoint (bv_unsigned destination)
      (length bytes) (bv_unsigned source) (length bytes) by
    (unfold Inv_memcpy in Hinv; cbn in Hinv; tauto).
  have Hbacked : forall location,
      bv_unsigned destination <= location <
        bv_unsigned destination + Z.of_nat (length bytes) ->
      is_Some (global.(seq_mem) !! Z_to_bv 64 location) by
    (unfold Inv_memcpy in Hinv; cbn in Hinv; tauto).
  have Hframe : writeSuccessMemoryRangeFrame (bv_unsigned destination)
      (length bytes) global.(seq_mem) memoryFrame by
    (unfold Inv_memcpy in Hinv; cbn in Hinv; tauto).
  have Hlog : log = priorLog by
    (unfold Inv_memcpy in Hinv; cbn in Hinv; tauto).
  destruct (writeSuccessMemcpyInstructionFacts global Htable) as
    (HcodeD4 & HcodeD8 & HcodeDc & HcodeE0 & HcodeE4 & HcodeE8 &
     HcodeEc & HcodeF0 & HcodeF4).
  destruct ((proj2 (proj2 Hfacts)) "x15" ltac:(cbn; tauto)) as
    (oldX15 & Hx15).
  have Hmstatus : eval_a_exp regs writeSuccess15694Mstatus =
      Some (Val_Bool true) := proj1 Hfacts.
  destruct (segment_101d4 regs global (RVal_Bits oldX15) Hpc Hx15 HcodeD4
    HcodeD8 Hmstatus) as (HsegD4 & _).
  set initRegs := writeSuccess101d4Regs regs.
  have HinitFacts : writeSuccessWithdrawalsOperationalRegisterFacts initRegs by
    (apply writeSuccessMemcpyInitFacts; exact Hfacts).
  have Hready : writeSuccessMemcpyBytesReady initRegs global source destination
      (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat (length bytes))) bytes.
  { apply (writeSuccessMemcpyBytesReadyFromMemory initRegs global source
      destination (Z_to_bv 64 (Z.of_nat (length bytes))) bytes [] bytes).
    - reflexivity.
    - unfold initRegs, writeSuccess101d4Regs. rewrite lookup_insert.
      rewrite writeSuccess101d4NextPcExact. reflexivity.
    - unfold initRegs. rewrite writeSuccess101d4RegsLookupOther;
        try discriminate. exact Hx10.
    - unfold initRegs. rewrite writeSuccess101d4RegsLookupOther;
        try discriminate. exact Hx11.
    - unfold initRegs. rewrite writeSuccess101d4RegsLookupOther;
        try discriminate. exact Hx12.
    - unfold initRegs, writeSuccess101d4Regs. cbn. rewrite lookup_insert_ne;
        last discriminate. rewrite lookup_insert.
      replace (BV 64 0) with (Z_to_bv 64 (Z.of_nat 0)) by
        (apply bv_eq; bv_solve).
      reflexivity.
    - reflexivity.
    - exact Htable.
    - exact HinitFacts.
    - exact Hsource.
    - exact Hrange.
    - exact HsourceLower.
    - exact HsourceUpper.
    - exact HdestinationLower.
    - exact HdestinationUpper.
    - exact Hdisjoint.
    - exact Hbacked. }
  destruct (writeSuccessMemcpyBytesRun initRegs global source destination
    (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat (length bytes))) bytes Hready) as
    (loopSegments & HloopRun).
  set loopAfter := writeSuccessMemcpyBytesAfter initRegs global source
    destination (Z_to_bv 64 0) bytes.
  set finalRegs := loopAfter.1.(seq_regs).
  set finalGlobal := loopAfter.2.
  have HloopBoundary : loopAfter = writeSuccess101d8Before finalRegs finalGlobal.
  { unfold loopAfter, finalRegs, finalGlobal.
    apply writeSuccessMemcpyBytesAfterBoundary. }
  have HfinalPc : finalRegs !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x101d8)).
  { unfold finalRegs, loopAfter. apply writeSuccessMemcpyBytesAfterPc.
    unfold initRegs, writeSuccess101d4Regs. rewrite lookup_insert.
    rewrite writeSuccess101d4NextPcExact. reflexivity. }
  have HfinalX12 : finalRegs !! "x12" = Some
      (RVal_Bits (Z_to_bv 64 (Z.of_nat (length bytes)))).
  { unfold finalRegs, loopAfter.
    rewrite writeSuccessMemcpyBytesAfterLookupOther; try discriminate.
    unfold initRegs. rewrite writeSuccess101d4RegsLookupOther;
      try discriminate. exact Hx12. }
  have HfinalX15 : finalRegs !! "x15" = Some
      (RVal_Bits (Z_to_bv 64 (Z.of_nat (length bytes)))).
  { unfold finalRegs, loopAfter.
    rewrite writeSuccessMemcpyBytesAfterX15.
    - have Hsum :
          (Z_to_bv 64 0 + Z_to_bv 64 (Z.of_nat (length bytes)))%bv =
          Z_to_bv 64 (Z.of_nat (length bytes)) by
        (apply bv_eq; bv_solve).
      rewrite Hsum. reflexivity.
    - unfold initRegs, writeSuccess101d4Regs. rewrite lookup_insert_ne;
        last discriminate. rewrite lookup_insert.
      replace (BV 64 0) with (Z_to_bv 64 0) by (apply bv_eq; bv_solve).
      reflexivity. }
  have HfinalX1 : finalRegs !! "x1" = Some (RVal_Bits returnAddress).
  { unfold finalRegs, loopAfter.
    rewrite writeSuccessMemcpyBytesAfterLookupOther; try discriminate.
    unfold initRegs. rewrite writeSuccess101d4RegsLookupOther;
      try discriminate. exact Hx1. }
  have HfinalFacts : writeSuccessWithdrawalsOperationalRegisterFacts finalRegs.
  { unfold finalRegs, loopAfter. apply writeSuccessMemcpyBytesAfterFacts.
    exact HinitFacts. }
  have HfinalTable : writeSuccessWithdrawalsInstructionTable finalGlobal.
  { unfold finalGlobal, loopAfter. apply writeSuccessMemcpyBytesAfterTable.
    exact Htable. }
  have HfinalCodeD8 : finalGlobal.(seq_instrs) !! Z_to_bv 64 0x101d8 =
      Some IslaTraces.write_success_02.a101d8.a101d8 by
    (apply HfinalTable; unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap; cbn; tauto).
  have HfinalCodeDc : finalGlobal.(seq_instrs) !! Z_to_bv 64 0x101dc =
      Some IslaTraces.write_success_02.a101dc.a101dc by
    (apply HfinalTable; unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap; cbn; tauto).
  have HfinalMstatus : eval_a_exp finalRegs writeSuccess15694Mstatus =
      Some (Val_Bool true) := proj1 HfinalFacts.
  have HsegD8 := segment_101d8_fallthrough_mstatus finalRegs finalGlobal
    (Z_to_bv 64 (Z.of_nat (length bytes)))
    (Z_to_bv 64 (Z.of_nat (length bytes))) HfinalPc HfinalX15 HfinalX12
    ltac:(reflexivity) HfinalCodeD8 HfinalCodeDc HfinalMstatus.
  set returnRegs := writeSuccess101d8FallthroughRegs finalRegs.
  have HreturnPc : returnRegs !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x101dc)).
  { unfold returnRegs, writeSuccess101d8FallthroughRegs. rewrite lookup_insert.
    destruct writeSuccess101d8PcValues as (Hnext & _). rewrite Hnext. reflexivity. }
  have HreturnX1 : returnRegs !! "x1" = Some (RVal_Bits returnAddress).
  { unfold returnRegs, writeSuccess101d8FallthroughRegs.
    rewrite lookup_insert_ne; [exact HfinalX1|discriminate]. }
  have HreturnMstatus : eval_a_exp returnRegs writeSuccess15694Mstatus =
      Some (Val_Bool true).
  { unfold returnRegs, writeSuccess101d8FallthroughRegs,
      writeSuccess15694Mstatus in HfinalMstatus |- *. cbn in *.
    rewrite lookup_insert_ne; [exact HfinalMstatus|discriminate]. }
  have HreturnAlign := writeSuccessMemcpyReturnAlignmentEval returnRegs
    returnAddress HreturnX1 Halign.
  destruct (segment_101dc returnRegs finalGlobal returnAddress HreturnPc
    HreturnX1 HfinalCodeDc HreturnMstatus HreturnAlign) as
    (HsegDc & HsegDcMemory).
  have HreturnLookup : finalGlobal.(seq_instrs) !! returnAddress <> None.
  { destruct Hreturn as (returnTrace & Hreturn).
    unfold finalGlobal, loopAfter.
    rewrite writeSuccessMemcpyBytesAfterInstrs. rewrite Hreturn. discriminate. }
  have HdestinationZero : (destination + Z_to_bv 64 0)%bv =
      Z_to_bv 64 (bv_unsigned destination).
  { rewrite Z_to_bv_bv_unsigned. apply bv_eq. bv_solve. }
  exists (writeSuccess101d4Observations regs global :: loopSegments ++
      [writeSuccess101d8FallthroughAllObservations
         (Z_to_bv 64 (Z.of_nat (length bytes)))
         (Z_to_bv 64 (Z.of_nat (length bytes))) finalRegs finalGlobal;
       writeSuccess101dcObservations returnRegs finalGlobal returnAddress]),
    (writeSuccess101dcAfter returnRegs finalGlobal returnAddress, priorLog).
  split.
  { change (IslaInstructionRun (7 * length bytes)
      (writeSuccess101d8Before initRegs global) loopSegments loopAfter)
      in HloopRun.
    rewrite HloopBoundary in HloopRun.
    have Hfirst : IslaInstructionRun 1 (writeSuccess101d4Before regs global)
        [writeSuccess101d4Observations regs global]
        (writeSuccess101d4After regs global).
    { econstructor; first exact HsegD4. constructor. }
    have Hprefix := islaInstructionRun_app _ _ _ _ _ _ _ Hfirst HloopRun.
    have HwithFall := islaInstructionRun_snoc _ _ _ _ _ _ Hprefix HsegD8.
    have Hfull := islaInstructionRun_snoc _ _ _ _ _ _ HwithFall HsegDc.
    replace (7 * length bytes + 3)%nat with
      (S (S (1 + 7 * length bytes)))%nat by lia.
    rewrite <- app_assoc in Hfull.
    cbn [app] in Hfull.
    exact Hfull. }
  split.
  { unfold writeSuccessWithdrawalsConcretePc. cbn.
    destruct Hreturn as (returnTrace & Hreturn).
    have HreturnFinal : finalGlobal.(seq_instrs) !! returnAddress =
        Some returnTrace.
    { unfold finalGlobal, loopAfter.
      rewrite writeSuccessMemcpyBytesAfterInstrs. exact Hreturn. }
    unfold writeSuccess101dcAfter.
    rewrite (writeSuccessMemcpyReturnTargetExact returnAddress Halign).
    rewrite HreturnFinal.
    cbn. unfold writeSuccess101dcRegs. rewrite lookup_insert.
    rewrite writeSuccessMemcpyReturnTargetExact; [reflexivity|exact Halign]. }
  split.
  { have Hmemory := writeSuccessMemcpyBytesAfterMemory initRegs global source
      destination (Z_to_bv 64 0) bytes 0 ltac:(reflexivity)
      ltac:(pose proof (bv_unsigned_in_range 64 destination); lia)
      ltac:(unfold islaMemoryRange in Hrange; cbn in *; lia).
    rewrite HsegDcMemory.
    unfold finalGlobal, loopAfter in Hmemory. cbn.
    rewrite Hmemory. rewrite HdestinationZero.
    apply read_mem_list_written. exact Hrange. }
  split.
  { have Hupdate := writeSuccessMemcpyMemoryUpdate global.(seq_mem)
      (bv_unsigned source) (bv_unsigned destination) bytes Hsource Hrange
      Hdisjoint Hbacked.
    have Hmemory := writeSuccessMemcpyBytesAfterMemory initRegs global source
      destination (Z_to_bv 64 0) bytes 0 ltac:(reflexivity)
      ltac:(pose proof (bv_unsigned_in_range 64 destination); lia)
      ltac:(unfold islaMemoryRange in Hrange; cbn in *; lia).
    rewrite HsegDcMemory.
    cbn in Hupdate. unfold finalGlobal, loopAfter in Hmemory. cbn.
    rewrite Hmemory. rewrite HdestinationZero. exact (proj1 (proj2 Hupdate)). }
  split.
  { have Hmemory := writeSuccessMemcpyBytesAfterMemory initRegs global source
      destination (Z_to_bv 64 0) bytes 0 ltac:(reflexivity)
      ltac:(pose proof (bv_unsigned_in_range 64 destination); lia)
      ltac:(unfold islaMemoryRange in Hrange; cbn in *; lia).
    rewrite HsegDcMemory.
    unfold finalGlobal, loopAfter in Hmemory. cbn.
    rewrite Hmemory. rewrite HdestinationZero.
    eapply writeSuccessMemoryRangeFrameWrite; eassumption. }
  reflexivity.
Qed.

Print Assumptions block_memcpy.
