From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessInstructionRunSplit.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101dc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101dcCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyAfter.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyBoundaryFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyPositions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyEntry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyInduction.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyReadiness.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyRecords.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.
Open Scope Z_scope.

Local Opaque writeSuccessMemoryRangeFrame.

Theorem writeSuccessWithdrawalsBlockMemcpyPositionGroups :
  forall destination source returnAddress bytes destinationBefore memoryFrame
      priorLog state segments after,
    Inv_memcpy destination source returnAddress bytes destinationBefore
      memoryFrame priorLog state ->
    WriteSuccessWithdrawalsRecordedRun (7 * length bytes + 3)
      state segments after ->
    writeSuccessWithdrawalsConcretePc after = Some (bv_unsigned returnAddress) /\
    read_mem_list after.1.2.(seq_mem) (bv_unsigned destination)
      (N.of_nat (length bytes)) = Some bytes /\
    read_mem_list after.1.2.(seq_mem) (bv_unsigned source)
      (N.of_nat (length bytes)) = Some bytes /\
    writeSuccessMemoryRangeFrame (bv_unsigned destination) (length bytes)
      after.1.2.(seq_mem) memoryFrame /\
    after.2 = priorLog /\
    exists regs global returnTrace,
      state.1 = writeSuccess101d4Before regs global /\
      global.(seq_instrs) !! returnAddress = Some returnTrace /\
      after.1 =
        (writeSuccess15694Local returnTrace
          (writeSuccessMemcpyEndpointRegs regs global source destination bytes
            returnAddress),
         writeSuccessMemcpyEndpointGlobal regs global source destination bytes) /\
      exists obsD4 loopSegments obsD8 obsDc,
        segments = [obsD4] ++ loopSegments ++ [obsD8; obsDc] /\
        WriteSuccessWithdrawalsRecordedRun 1 state [obsD4]
          (writeSuccess101d4After regs global, priorLog) /\
        WriteSuccessWithdrawalsPositionEdges loopSegments
          (writeSuccessMemcpyBytesPositionStates (writeSuccess101d4Regs regs)
            global source destination (Z_to_bv 64 0)
            (Z_to_bv 64 (Z.of_nat (length bytes))) bytes priorLog) /\
        WriteSuccessWithdrawalsRecordedRun 1
          (writeSuccessMemcpyLoopAfter regs global source destination bytes,
           priorLog) [obsD8]
          (writeSuccess101d8FallthroughAfter
            (writeSuccessMemcpyLoopAfter regs global source destination bytes).1.(seq_regs)
            (writeSuccessMemcpyEndpointGlobal regs global source destination bytes),
           priorLog) /\
        WriteSuccessWithdrawalsRecordedRun 1
          (writeSuccess101d8FallthroughAfter
            (writeSuccessMemcpyLoopAfter regs global source destination bytes).1.(seq_regs)
            (writeSuccessMemcpyEndpointGlobal regs global source destination bytes),
           priorLog) [obsDc] after.
Proof.
  intros destination source returnAddress bytes destinationBefore memoryFrame
    priorLog state segments after Hinv Hrecorded.
  destruct state as [machine log].
  destruct after as [afterMachine afterLog].
  destruct Hrecorded as (Hrun & HafterLog).
  destruct (writeSuccessMemcpyEntryShape destination source returnAddress bytes
    destinationBefore memoryFrame priorLog (machine, log) Hinv) as
    (regs & global & Hmachine).
  cbn in Hmachine. subst machine.
  have Hboundary : IslaInstructionBoundary (writeSuccess101d4Before regs global)
      by (unfold Inv_memcpy in Hinv; cbn in Hinv; tauto).
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
  replace (7 * length bytes + 3)%nat with
      (1 + (7 * length bytes + 2))%nat in Hrun by lia.
  destruct (islaInstructionRun_split 1 (7 * length bytes + 2) _ _ _ Hrun) as
    (firstSegments & afterD4 & restSegments & Hsegments & Hfirst & Hrest).
  inversion Hfirst as [|? ? obsD4 ? ? ? HsegD4 Hzero]; subst.
  inversion Hzero; subst.
  destruct (segment_101d4_covered regs global (RVal_Bits oldX15) obsD4 afterD4
    Hpc Hx15 HcodeD4 HcodeD8 Hmstatus HsegD4) as (HafterD4 & HobsD4).
  subst afterD4.
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
  destruct (islaInstructionRun_split (7 * length bytes) 2 _ _ _ Hrest) as
    (loopSegments & loopAfter & tailSegments & HrestSegments & Hloop & Htail).
  destruct (writeSuccessMemcpyBytesRunCoveredWithRecords initRegs global source
    destination (Z_to_bv 64 0)
    (Z_to_bv 64 (Z.of_nat (length bytes))) bytes loopSegments loopAfter
    Hready Hloop) as (HloopAfter & HloopRecords).
  destruct (writeSuccessMemcpyBytesPositionPath initRegs global source destination
    (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat (length bytes))) bytes priorLog
    loopSegments loopAfter Hready Hloop) as (HloopAfterPosition & HloopEdges).
  subst loopAfter.
  set loopAfter := writeSuccessMemcpyBytesAfter initRegs global source
    destination (Z_to_bv 64 0) bytes.
  set finalRegs := loopAfter.1.(seq_regs).
  set finalGlobal := loopAfter.2.
  have HloopBoundary : loopAfter = writeSuccess101d8Before finalRegs finalGlobal
    by (unfold loopAfter, finalRegs, finalGlobal;
        apply writeSuccessMemcpyBytesAfterBoundary).
  fold loopAfter in Htail.
  rewrite HloopBoundary in Htail.
  inversion Htail as [|? ? obsD8 afterD8 ? ? HsegD8 Hlast]; subst.
  inversion Hlast as [|? ? obsDc afterDc ? ? HsegDc Hzero2]; subst.
  inversion Hzero2; subst.
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
  { unfold finalRegs, loopAfter. rewrite writeSuccessMemcpyBytesAfterX15.
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
  have HfinalCodeE0 : finalGlobal.(seq_instrs) !! Z_to_bv 64 0x101e0 =
      Some IslaTraces.write_success_02.a101e0.a101e0 by
    (apply HfinalTable; unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap; cbn; tauto).
  have HfinalMstatus : eval_a_exp finalRegs writeSuccess15694Mstatus =
      Some (Val_Bool true) := proj1 HfinalFacts.
  destruct (segment_101d8_covered finalRegs finalGlobal
    (Z_to_bv 64 (Z.of_nat (length bytes)))
    (Z_to_bv 64 (Z.of_nat (length bytes))) obsD8 afterD8 HfinalPc HfinalX15
    HfinalX12 HfinalCodeD8 HfinalCodeDc HfinalCodeE0 HfinalMstatus HsegD8) as
    (HafterD8 & HobsD8).
  unfold writeSuccess101d8After in HafterD8.
  unfold writeSuccess101d8Observations in HobsD8.
  destruct (decide
    (Z_to_bv 64 (Z.of_nat (length bytes)) =
     Z_to_bv 64 (Z.of_nat (length bytes)))); last contradiction.
  subst afterD8.
  set returnRegs := writeSuccess101d8FallthroughRegs finalRegs.
  have HreturnPc : returnRegs !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x101dc)).
  { unfold returnRegs, writeSuccess101d8FallthroughRegs. rewrite lookup_insert.
    destruct writeSuccess101d8PcValues as (Hnext & _). rewrite Hnext.
    reflexivity. }
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
  destruct (segment_101dc_covered returnRegs finalGlobal returnAddress obsDc
    afterMachine HreturnPc HreturnX1 HfinalCodeDc HreturnMstatus HreturnAlign
    HsegDc) as (HafterMachine & HobsDc).
  subst afterMachine.
  destruct Hreturn as (returnTrace & Hreturn).
  have HreturnFinal : finalGlobal.(seq_instrs) !! returnAddress =
      Some returnTrace.
  { unfold finalGlobal, loopAfter.
    rewrite writeSuccessMemcpyBytesAfterInstrs. exact Hreturn. }
  have HrecordsD4 : segmentRecords (writeSuccess101d4Before regs global)
      (writeSuccess101d4Observations regs global) = [].
  { apply writeSuccessSegmentRecordsEmpty. reflexivity. }
  have HrecordsD8 : segmentRecords
      (writeSuccess101d8Before finalRegs finalGlobal)
      (writeSuccess101d8FallthroughAllObservations
        (Z_to_bv 64 (Z.of_nat (length bytes)))
        (Z_to_bv 64 (Z.of_nat (length bytes))) finalRegs finalGlobal) = [].
  { apply writeSuccessSegmentRecordsEmpty. reflexivity. }
  have HrecordsDc : segmentRecords (writeSuccess101dcBefore returnRegs finalGlobal)
      (writeSuccess101dcObservations returnRegs finalGlobal returnAddress) = [].
  { apply writeSuccessSegmentRecordsEmpty.
    unfold writeSuccess101dcObservations, writeSuccess101dcPrefixObservations,
      writeSuccess101dcLocals, writeSuccess15694Observation,
      writeSuccess101dcDoneLabels. cbn.
    rewrite (writeSuccessMemcpyReturnTargetExact returnAddress Halign).
    rewrite HreturnFinal. reflexivity. }
  subst obsD8 obsDc.
  have Hrecords : segmentRecords (writeSuccess101d4Before regs global)
      (flattenMicroObservations
        ([writeSuccess101d4Observations regs global] ++ loopSegments ++
         [writeSuccess101d8FallthroughAllObservations
            (Z_to_bv 64 (Z.of_nat (length bytes)))
            (Z_to_bv 64 (Z.of_nat (length bytes))) finalRegs finalGlobal;
          writeSuccess101dcObservations returnRegs finalGlobal returnAddress])) = [].
  {
    rewrite flattenMicroObservationsApp.
    rewrite (segmentRecords_app (writeSuccess101d4Before regs global)
      (flattenMicroObservations [writeSuccess101d4Observations regs global])
      (writeSuccess101d4After regs global)
      (flattenMicroObservations (loopSegments ++
        [writeSuccess101d8FallthroughAllObservations
           (Z_to_bv 64 (Z.of_nat (length bytes)))
           (Z_to_bv 64 (Z.of_nat (length bytes))) finalRegs finalGlobal;
         writeSuccess101dcObservations returnRegs finalGlobal returnAddress]))).
    2: exact (islaInstructionRunCorrespondence 1 _ _ _ Hfirst).
    cbn [flattenMicroObservations] in HrecordsD4 |- *.
    rewrite HrecordsD4.
    rewrite flattenMicroObservationsApp.
    rewrite (segmentRecords_app (writeSuccess101d4After regs global)
      (flattenMicroObservations loopSegments)
      (writeSuccess101d8Before finalRegs finalGlobal)
      (flattenMicroObservations
        [writeSuccess101d8FallthroughAllObservations
          (Z_to_bv 64 (Z.of_nat (length bytes)))
          (Z_to_bv 64 (Z.of_nat (length bytes))) finalRegs finalGlobal;
         writeSuccess101dcObservations returnRegs finalGlobal returnAddress])).
    2: { have HloopPath :=
          islaInstructionRunCorrespondence _ _ _ _ Hloop.
         fold loopAfter in HloopPath.
         rewrite HloopBoundary in HloopPath. exact HloopPath. }
    rewrite HloopRecords.
    change (segmentRecords (writeSuccess101d8Before finalRegs finalGlobal)
      (flattenMicroObservations
        ([writeSuccess101d8FallthroughAllObservations
            (Z_to_bv 64 (Z.of_nat (length bytes)))
            (Z_to_bv 64 (Z.of_nat (length bytes))) finalRegs finalGlobal] ++
         [writeSuccess101dcObservations returnRegs finalGlobal returnAddress])) = []).
    rewrite flattenMicroObservationsApp.
    rewrite (segmentRecords_app (writeSuccess101d8Before finalRegs finalGlobal)
      (flattenMicroObservations
        [writeSuccess101d8FallthroughAllObservations
          (Z_to_bv 64 (Z.of_nat (length bytes)))
          (Z_to_bv 64 (Z.of_nat (length bytes))) finalRegs finalGlobal])
      (writeSuccess101d8FallthroughAfter finalRegs finalGlobal)
      (flattenMicroObservations
        [writeSuccess101dcObservations returnRegs finalGlobal returnAddress])).
    2: { apply islaInstructionSegmentCorrespondence. exact HsegD8. }
    cbn [flattenMicroObservations] in HrecordsD8, HrecordsDc |- *.
    rewrite HrecordsD8. rewrite HrecordsDc. reflexivity. }
  have HafterLogFinal : afterLog = priorLog.
  { cbn in HafterLog.
    change (afterLog = priorLog ++
      segmentRecords (writeSuccess101d4Before regs global)
        (flattenMicroObservations
          ([writeSuccess101d4Observations regs global] ++ loopSegments ++
           [writeSuccess101d8FallthroughAllObservations
              (Z_to_bv 64 (Z.of_nat (length bytes)))
              (Z_to_bv 64 (Z.of_nat (length bytes))) finalRegs finalGlobal;
            writeSuccess101dcObservations returnRegs finalGlobal
              returnAddress]))) in HafterLog.
    rewrite Hrecords in HafterLog. rewrite app_nil_r in HafterLog.
    exact HafterLog. }
  have HdestinationZero : (destination + Z_to_bv 64 0)%bv =
      Z_to_bv 64 (bv_unsigned destination).
  { rewrite Z_to_bv_bv_unsigned. apply bv_eq. bv_solve. }
  have Hmemory := writeSuccessMemcpyBytesAfterMemory initRegs global source
    destination (Z_to_bv 64 0) bytes 0 ltac:(reflexivity)
    ltac:(pose proof (bv_unsigned_in_range 64 destination); lia)
    ltac:(unfold islaMemoryRange in Hrange; cbn in *; lia).
  unfold writeSuccess101dcAfter.
  rewrite (writeSuccessMemcpyReturnTargetExact returnAddress Halign).
  rewrite HreturnFinal. cbn.
  split.
  { unfold writeSuccessWithdrawalsConcretePc. cbn.
    unfold writeSuccess101dcRegs. rewrite lookup_insert.
    rewrite writeSuccessMemcpyReturnTargetExact; [reflexivity|exact Halign]. }
  split.
  { unfold finalGlobal, loopAfter in Hmemory. cbn. rewrite Hmemory.
    rewrite HdestinationZero. apply read_mem_list_written. exact Hrange. }
  split.
  { have Hupdate := writeSuccessMemcpyMemoryUpdate global.(seq_mem)
      (bv_unsigned source) (bv_unsigned destination) bytes Hsource Hrange
      Hdisjoint Hbacked.
    cbn in Hupdate. unfold finalGlobal, loopAfter in Hmemory. cbn.
    rewrite Hmemory. rewrite HdestinationZero. exact (proj1 (proj2 Hupdate)). }
  split.
  { unfold finalGlobal, loopAfter in Hmemory. cbn. rewrite Hmemory.
    rewrite HdestinationZero.
    eapply writeSuccessMemoryRangeFrameWrite; eassumption. }
  split; first exact HafterLogFinal.
  exists regs, global, returnTrace. split; first reflexivity.
  split; first exact Hreturn.
  split.
  { unfold writeSuccessMemcpyEndpointRegs, writeSuccessMemcpyEndpointGlobal,
      writeSuccessMemcpyLoopAfter, returnRegs, finalRegs, finalGlobal, loopAfter,
      initRegs. reflexivity. }
  have HedgeD4 : WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccess101d4Before regs global, priorLog)
      [writeSuccess101d4Observations regs global]
      (writeSuccess101d4After regs global, priorLog).
  { pose proof (writeSuccessWithdrawalsRecordedRunOne
      (writeSuccess101d4Before regs global, priorLog)
      (writeSuccess101d4Observations regs global)
      (writeSuccess101d4After regs global) HsegD4) as Hedge.
    rewrite HrecordsD4 in Hedge. cbn in Hedge. rewrite app_nil_r in Hedge.
    exact Hedge. }
  have HedgeD8 : WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccess101d8Before finalRegs finalGlobal, priorLog)
      [writeSuccess101d8FallthroughAllObservations
        (Z_to_bv 64 (Z.of_nat (length bytes)))
        (Z_to_bv 64 (Z.of_nat (length bytes))) finalRegs finalGlobal]
      (writeSuccess101d8FallthroughAfter finalRegs finalGlobal, priorLog).
  { pose proof (writeSuccessWithdrawalsRecordedRunOne
      (writeSuccess101d8Before finalRegs finalGlobal, priorLog)
      (writeSuccess101d8FallthroughAllObservations
        (Z_to_bv 64 (Z.of_nat (length bytes)))
        (Z_to_bv 64 (Z.of_nat (length bytes))) finalRegs finalGlobal)
      (writeSuccess101d8FallthroughAfter finalRegs finalGlobal) HsegD8) as Hedge.
    rewrite HrecordsD8 in Hedge. cbn in Hedge. rewrite app_nil_r in Hedge.
    exact Hedge. }
  have HedgeDc : WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccess101dcBefore returnRegs finalGlobal, priorLog)
      [writeSuccess101dcObservations returnRegs finalGlobal returnAddress]
      (writeSuccess101dcAfter returnRegs finalGlobal returnAddress, priorLog).
  { pose proof (writeSuccessWithdrawalsRecordedRunOne
      (writeSuccess101dcBefore returnRegs finalGlobal, priorLog)
      (writeSuccess101dcObservations returnRegs finalGlobal returnAddress)
      (writeSuccess101dcAfter returnRegs finalGlobal returnAddress) HsegDc) as Hedge.
    rewrite HrecordsDc in Hedge. cbn in Hedge. rewrite app_nil_r in Hedge.
    exact Hedge. }
  subst afterLog.
  exists (writeSuccess101d4Observations regs global), loopSegments,
    (writeSuccess101d8FallthroughAllObservations
      (Z_to_bv 64 (Z.of_nat (length bytes)))
      (Z_to_bv 64 (Z.of_nat (length bytes))) finalRegs finalGlobal),
    (writeSuccess101dcObservations returnRegs finalGlobal returnAddress).
  split.
  { reflexivity. }
  split; first exact HedgeD4.
  split.
  { unfold initRegs in HloopEdges. exact HloopEdges. }
  split.
  { change (WriteSuccessWithdrawalsRecordedRun 1 (loopAfter, priorLog)
      [writeSuccess101d8FallthroughAllObservations
        (Z_to_bv 64 (Z.of_nat (length bytes)))
        (Z_to_bv 64 (Z.of_nat (length bytes))) finalRegs finalGlobal]
      (writeSuccess101d8FallthroughAfter finalRegs finalGlobal, priorLog)).
    rewrite HloopBoundary. exact HedgeD8. }
  have HdcEndpoint : writeSuccess101dcAfter returnRegs finalGlobal returnAddress =
      (writeSuccess15694Local returnTrace
        (writeSuccess101dcRegs returnRegs returnAddress), finalGlobal).
  { unfold writeSuccess101dcAfter.
    rewrite (writeSuccessMemcpyReturnTargetExact returnAddress Halign).
    rewrite HreturnFinal. reflexivity. }
  rewrite <- HdcEndpoint.
  change (WriteSuccessWithdrawalsRecordedRun 1
    (writeSuccess101dcBefore returnRegs finalGlobal, priorLog)
    [writeSuccess101dcObservations returnRegs finalGlobal returnAddress]
    (writeSuccess101dcAfter returnRegs finalGlobal returnAddress, priorLog)).
  exact HedgeDc.
Qed.

Print Assumptions writeSuccessWithdrawalsBlockMemcpyPositionGroups.
