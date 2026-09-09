From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101ec.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e0Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e8Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101ecCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f0Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f4Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyByteRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyRecords.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyAssumes.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyState.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessMemcpyByteState1 regs global :=
  writeSuccess101d8TakenAfter regs global.
Definition writeSuccessMemcpyByteState2 regs global source index :=
  writeSuccess101e0After
    (writeSuccessMemcpyByteRegs1 regs) global source index.
Definition writeSuccessMemcpyByteState3 regs global source index byte :=
  writeSuccess101e4After (writeSuccessMemcpyByteRegs2 regs source index) global byte.
Definition writeSuccessMemcpyByteState4 regs global source destination index byte :=
  writeSuccess101e8After (writeSuccessMemcpyByteRegs3 regs source index byte)
    global destination index.
Definition writeSuccessMemcpyByteState5 regs global source destination index byte :=
  writeSuccess101ecAfter
    (writeSuccessMemcpyByteRegs4 regs source destination index byte) global index.
Definition writeSuccessMemcpyByteState6 regs global source destination index byte :=
  writeSuccess101f0After
    (writeSuccessMemcpyByteRegs5 regs source destination index byte) global
    (writeSuccessMemcpyDestinationAddress destination index)
    (writeSuccess101e4Loaded byte).

Theorem writeSuccessMemcpyBytePositionsExact regs global
    (source destination index length : bv 64) (byte : bv 8)
    priorLog segments after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  regs !! "x10" = Some (RVal_Bits destination) ->
  regs !! "x11" = Some (RVal_Bits source) ->
  regs !! "x12" = Some (RVal_Bits length) ->
  regs !! "x15" = Some (RVal_Bits index) ->
  index <> length ->
  writeSuccessWithdrawalsInstructionTable global ->
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  read_mem global.(seq_mem)
    (bv_unsigned (writeSuccessMemcpySourceAddress source index)) 1 =
    Some (bv_to_bvn byte) ->
  0x20000000 <= bv_unsigned (writeSuccessMemcpySourceAddress source index) ->
  bv_unsigned (writeSuccessMemcpySourceAddress source index) + 1 <= 0x40000000 ->
  0x20000000 <= bv_unsigned
    (writeSuccessMemcpyDestinationAddress destination index) ->
  bv_unsigned (writeSuccessMemcpyDestinationAddress destination index) + 1 <=
    0x40000000 ->
  is_Some (global.(seq_mem) !!
    writeSuccessMemcpyDestinationAddress destination index) ->
  IslaInstructionRun 7 (writeSuccess101d8Before regs global) segments after ->
  exists observations0 observations1 observations2 observations3
      observations4 observations5 observations6,
    segments = [observations0; observations1; observations2; observations3;
      observations4; observations5; observations6] /\
    after = writeSuccessMemcpyByteAfter regs global source destination index byte /\
    segmentRecords (writeSuccess101d8Before regs global)
      (flattenMicroObservations segments) = [] /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccess101d8Before regs global, priorLog) [observations0]
      (writeSuccessMemcpyByteState1 regs global,
       priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccessMemcpyByteState1 regs global,
       priorLog) [observations1]
      (writeSuccessMemcpyByteState2 regs global source index,
       priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccessMemcpyByteState2 regs global source index,
       priorLog) [observations2]
      (writeSuccessMemcpyByteState3 regs global source index byte,
       priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccessMemcpyByteState3 regs global source index byte,
       priorLog) [observations3]
      (writeSuccessMemcpyByteState4 regs global source destination index byte,
       priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccessMemcpyByteState4 regs global source destination index byte,
       priorLog) [observations4]
      (writeSuccessMemcpyByteState5 regs global source destination index byte,
       priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccessMemcpyByteState5 regs global source destination index byte,
       priorLog) [observations5]
      (writeSuccessMemcpyByteState6 regs global source destination index byte,
       priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccessMemcpyByteState6 regs global source destination index byte,
       priorLog) [observations6]
      (writeSuccessMemcpyByteAfter regs global source destination index byte,
       priorLog).
Proof.
  intros Hpc Hx10 Hx11 Hx12 Hx15 Hne Htable Hfacts HsourceRead
    HsourceLower HsourceUpper HdestinationLower HdestinationUpper
    HdestinationBacked Hrun.
  destruct (writeSuccessMemcpyInstructionFacts global Htable) as
    (HcodeD4 & HcodeD8 & HcodeDc & HcodeE0 & HcodeE4 & HcodeE8 &
     HcodeEc & HcodeF0 & HcodeF4).
  destruct (writeSuccessMemcpyRegisterFacts regs Hfacts) as
    (mstatus0 & satp0 & oldX13 & oldX14 & Hx13 & Hx14 & Hmstatus0 &
     Hsatp0 & HsysE40 & HsysF00 & Hassume0).
  have Hfacts1 := writeSuccessMemcpyByteRegs1OperationalFacts regs Hfacts.
  have Hassume1 : eval_a_exp (writeSuccessMemcpyByteRegs1 regs)
      writeSuccess15694Mstatus = Some (Val_Bool true) := proj1 Hfacts1.
  have Hfacts2 := writeSuccessMemcpyByteRegs2OperationalFacts regs source index Hfacts.
  destruct (writeSuccessMemcpyRegisterFacts
    (writeSuccessMemcpyByteRegs2 regs source index) Hfacts2) as
    (mstatus2 & satp2 & x13At2 & x14At2 & Hx13At2 & Hx14At2 & Hmstatus2 &
     Hsatp2 & HsysE42 & HsysF02 & Hassume2).
  have HsourceAddress :
      writeSuccessMemcpyByteRegs2 regs source index !! "x13" =
        Some (RVal_Bits (writeSuccessMemcpySourceAddress source index)).
  { unfold writeSuccessMemcpyByteRegs2, writeSuccessMemcpyByteRegs1,
      writeSuccess101e0Regs, writeSuccessMemcpySourceAddress.
    rewrite lookup_insert_ne; last discriminate. rewrite lookup_insert.
    reflexivity. }
  have HloadAssumes := writeSuccessMemcpyLoadAssumes
    (writeSuccessMemcpyByteRegs2 regs source index)
    (writeSuccessMemcpySourceAddress source index) HsourceAddress
    (proj1 (proj2 (proj2 HsysE42)))
    (proj1 (proj2 (proj2 (proj2 HsysE42))))
    HsourceLower HsourceUpper.
  have Hfacts3 := writeSuccessMemcpyByteRegs3OperationalFacts
    regs source index byte Hfacts.
  have Hassume3 : eval_a_exp (writeSuccessMemcpyByteRegs3 regs source index byte)
      writeSuccess15694Mstatus = Some (Val_Bool true) := proj1 Hfacts3.
  have Hfacts4 := writeSuccessMemcpyByteRegs4OperationalFacts
    regs source destination index byte Hfacts.
  have Hassume4 : eval_a_exp
      (writeSuccessMemcpyByteRegs4 regs source destination index byte)
      writeSuccess15694Mstatus = Some (Val_Bool true) := proj1 Hfacts4.
  have Hfacts5 := writeSuccessMemcpyByteRegs5OperationalFacts
    regs source destination index byte Hfacts.
  destruct (writeSuccessMemcpyRegisterFacts
    (writeSuccessMemcpyByteRegs5 regs source destination index byte) Hfacts5) as
    (mstatus5 & satp5 & x13At5 & x14At5 & Hx13At5 & Hx14At5 & Hmstatus5 &
     Hsatp5 & HsysE45 & HsysF05 & Hassume5).
  have HdestinationAddress :
      writeSuccessMemcpyByteRegs5 regs source destination index byte !! "x14" =
        Some (RVal_Bits
          (writeSuccessMemcpyDestinationAddress destination index)).
  { unfold writeSuccessMemcpyByteRegs5, writeSuccessMemcpyByteRegs4,
      writeSuccess101ecRegs, writeSuccess101e8Regs,
      writeSuccessMemcpyDestinationAddress.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate. rewrite lookup_insert.
    reflexivity. }
  have HstoreAssumes := writeSuccessMemcpyStoreAssumes
    (writeSuccessMemcpyByteRegs5 regs source destination index byte)
    (writeSuccessMemcpyDestinationAddress destination index)
    HdestinationAddress (proj1 (proj2 (proj2 HsysF05)))
    (proj1 (proj2 (proj2 (proj2 HsysF05))))
    HdestinationLower HdestinationUpper.
  have HdestinationRange :
      0 <= bv_unsigned (writeSuccessMemcpyDestinationAddress destination index) <
        2 ^ 64.
  { pose proof (bv_unsigned_in_range 64
      (writeSuccessMemcpyDestinationAddress destination index)).
    unfold bv_modulus in *. cbn in *. lia. }
  destruct (writeSuccessMemcpyBackedByte global.(seq_mem)
    (bv_unsigned (writeSuccessMemcpyDestinationAddress destination index))
    HdestinationRange) as (oldByte & HoldByte).
  { rewrite Z_to_bv_bv_unsigned. exact HdestinationBacked. }
  have Hfacts6 := writeSuccessMemcpyByteRegs6OperationalFacts
    regs source destination index byte Hfacts.
  have Hassume6 : eval_a_exp
      (writeSuccessMemcpyByteRegs6 regs source destination index byte)
      writeSuccess15694Mstatus = Some (Val_Bool true) := proj1 Hfacts6.
  inversion Hrun as [|c0 before0 obs0 middle0 rest0 final0 Hseg0 Hrun1]; subst.
  inversion Hrun1 as [|c1 before1 obs1 middle1 rest1 final1 Hseg1 Hrun2]; subst.
  inversion Hrun2 as [|c2 before2 obs2 middle2 rest2 final2 Hseg2 Hrun3]; subst.
  inversion Hrun3 as [|c3 before3 obs3 middle3 rest3 final3 Hseg3 Hrun4]; subst.
  inversion Hrun4 as [|c4 before4 obs4 middle4 rest4 final4 Hseg4 Hrun5]; subst.
  inversion Hrun5 as [|c5 before5 obs5 middle5 rest5 final5 Hseg5 Hrun6]; subst.
  inversion Hrun6 as [|c6 before6 obs6 middle6 rest6 final6 Hseg6 Hrun7]; subst.
  inversion Hrun7; subst.
  destruct (segment_101d8_covered regs global index length obs0 middle0
    Hpc Hx15 Hx12 HcodeD8 HcodeDc HcodeE0 Hassume0 Hseg0) as (Hmiddle0 & Hobs0).
  unfold writeSuccess101d8After in Hmiddle0.
  destruct (decide (index = length)); first contradiction. subst middle0.
  destruct (segment_101e0_covered (writeSuccessMemcpyByteRegs1 regs) global
    source index (RVal_Bits oldX13) obs1 middle1
    ltac:(unfold writeSuccessMemcpyByteRegs1, writeSuccess101d8TakenRegs;
      rewrite lookup_insert; reflexivity)
    ltac:(unfold writeSuccessMemcpyByteRegs1, writeSuccess101d8TakenRegs;
      rewrite lookup_insert_ne; try discriminate; exact Hx11)
    ltac:(unfold writeSuccessMemcpyByteRegs1, writeSuccess101d8TakenRegs;
      rewrite lookup_insert_ne; try discriminate; exact Hx15)
    ltac:(unfold writeSuccessMemcpyByteRegs1, writeSuccess101d8TakenRegs;
      rewrite lookup_insert_ne; try discriminate; exact Hx13)
    HcodeE0 HcodeE4 Hassume1 Hseg1) as (Hmiddle1 & Hobs1).
  subst middle1.
  destruct (segment_101e4_covered
    (writeSuccessMemcpyByteRegs2 regs source index) global mstatus2
    (writeSuccessMemcpySourceAddress source index) satp2 byte obs2 middle2
    ltac:(unfold writeSuccessMemcpyByteRegs2, writeSuccess101e0Regs;
      rewrite lookup_insert; reflexivity)
    HsourceAddress Hmstatus2 Hsatp2 HsysE42 HsourceRead HcodeE4 HcodeE8
    Hassume2 (proj1 HloadAssumes) (proj2 HloadAssumes) Hseg2) as
    (Hmiddle2 & Hobs2).
  subst middle2.
  destruct (segment_101e8_covered
    (writeSuccessMemcpyByteRegs3 regs source index byte) global destination index
    (RVal_Bits oldX14) obs3 middle3
    ltac:(unfold writeSuccessMemcpyByteRegs3, writeSuccess101e4Regs;
      rewrite lookup_insert; reflexivity)
    ltac:(unfold writeSuccessMemcpyByteRegs3;
      rewrite writeSuccess101e4RegsLookupOther; try discriminate;
      unfold writeSuccessMemcpyByteRegs2;
      rewrite writeSuccess101e0RegsLookupOther; try discriminate;
      unfold writeSuccessMemcpyByteRegs1, writeSuccess101d8TakenRegs;
      rewrite lookup_insert_ne; try discriminate; exact Hx10)
    ltac:(unfold writeSuccessMemcpyByteRegs3;
      rewrite writeSuccess101e4RegsLookupOther; try discriminate;
      unfold writeSuccessMemcpyByteRegs2;
      rewrite writeSuccess101e0RegsLookupOther; try discriminate;
      unfold writeSuccessMemcpyByteRegs1, writeSuccess101d8TakenRegs;
      rewrite lookup_insert_ne; try discriminate; exact Hx15)
    ltac:(unfold writeSuccessMemcpyByteRegs3;
      rewrite writeSuccess101e4RegsLookupOther; try discriminate;
      unfold writeSuccessMemcpyByteRegs2;
      rewrite writeSuccess101e0RegsLookupOther; try discriminate;
      unfold writeSuccessMemcpyByteRegs1, writeSuccess101d8TakenRegs;
      rewrite lookup_insert_ne; try discriminate; exact Hx14)
    HcodeE8 HcodeEc Hassume3 Hseg3) as (Hmiddle3 & Hobs3).
  subst middle3.
  destruct (segment_101ec_covered
    (writeSuccessMemcpyByteRegs4 regs source destination index byte) global index
    (RVal_Bits index) obs4 middle4
    ltac:(unfold writeSuccessMemcpyByteRegs4, writeSuccess101e8Regs;
      rewrite lookup_insert; reflexivity)
    ltac:(unfold writeSuccessMemcpyByteRegs4;
      rewrite writeSuccess101e8RegsLookupOther; try discriminate;
      unfold writeSuccessMemcpyByteRegs3;
      rewrite writeSuccess101e4RegsLookupOther; try discriminate;
      unfold writeSuccessMemcpyByteRegs2;
      rewrite writeSuccess101e0RegsLookupOther; try discriminate;
      unfold writeSuccessMemcpyByteRegs1, writeSuccess101d8TakenRegs;
      rewrite lookup_insert_ne; try discriminate; exact Hx15)
    ltac:(unfold writeSuccessMemcpyByteRegs4;
      rewrite writeSuccess101e8RegsLookupOther; try discriminate;
      unfold writeSuccessMemcpyByteRegs3;
      rewrite writeSuccess101e4RegsLookupOther; try discriminate;
      unfold writeSuccessMemcpyByteRegs2;
      rewrite writeSuccess101e0RegsLookupOther; try discriminate;
      unfold writeSuccessMemcpyByteRegs1, writeSuccess101d8TakenRegs;
      rewrite lookup_insert_ne; try discriminate; exact Hx15)
    HcodeEc HcodeF0 Hassume4 Hseg4) as (Hmiddle4 & Hobs4).
  subst middle4.
  destruct (segment_101f0_covered
    (writeSuccessMemcpyByteRegs5 regs source destination index byte) global
    mstatus5 (writeSuccessMemcpyDestinationAddress destination index) satp5
    (writeSuccess101e4Loaded byte) (bv_to_bvn oldByte) obs5 middle5
    ltac:(unfold writeSuccessMemcpyByteRegs5, writeSuccess101ecRegs;
      rewrite lookup_insert; reflexivity)
    HdestinationAddress Hmstatus5 Hsatp5
    ltac:(unfold writeSuccessMemcpyByteRegs5, writeSuccessMemcpyByteRegs4,
      writeSuccess101ecRegs, writeSuccess101e8Regs;
      rewrite lookup_insert_ne; try discriminate;
      rewrite lookup_insert_ne; try discriminate;
      rewrite lookup_insert_ne; try discriminate;
      rewrite lookup_insert_ne; try discriminate;
      unfold writeSuccessMemcpyByteRegs3, writeSuccess101e4Regs;
      rewrite lookup_insert_ne; try discriminate; rewrite lookup_insert; reflexivity)
    HsysF05 Hassume5 (proj1 HstoreAssumes) (proj2 HstoreAssumes)
    HoldByte HcodeF0 HcodeF4 Hseg5) as (result & Hmiddle5 & Hobs5).
  have Hlabels0 : concat (map microLabels
      (writeSuccess101d8Observations index length regs global)) = [].
  { unfold writeSuccess101d8Observations.
    destruct (decide (index = length)); first contradiction. reflexivity. }
  have Hlabels1 : concat (map microLabels
      (writeSuccess101e0Observations (writeSuccessMemcpyByteRegs1 regs)
        global source index)) = [] by reflexivity.
  have Hlabels2 : concat (map microLabels
      (writeSuccess101e4Observations
        (writeSuccessMemcpyByteRegs2 regs source index) global mstatus2
        (writeSuccessMemcpySourceAddress source index) satp2 byte)) = [] by
    reflexivity.
  have Hlabels3 : concat (map microLabels
      (writeSuccess101e8Observations
        (writeSuccessMemcpyByteRegs3 regs source index byte) global
        destination index)) = [] by reflexivity.
  have Hlabels4 : concat (map microLabels
      (writeSuccess101ecObservations
        (writeSuccessMemcpyByteRegs4 regs source destination index byte)
        global index)) = [] by reflexivity.
  have Hlabels5 : concat (map microLabels
      (writeSuccess101f0Observations
        (writeSuccessMemcpyByteRegs5 regs source destination index byte)
        global mstatus5
        (writeSuccessMemcpyDestinationAddress destination index) satp5
        (writeSuccess101e4Loaded byte) result)) = [] by reflexivity.
  have Hlabels6 : concat (map microLabels
      (writeSuccess101f4Observations
        (writeSuccessMemcpyByteRegs6 regs source destination index byte)
        (writeSuccess101f0Global global
          (writeSuccessMemcpyDestinationAddress destination index)
          (writeSuccess101e4Loaded byte)))) = [] by reflexivity.
  subst middle5.
  destruct (segment_101f4_covered
    (writeSuccessMemcpyByteRegs6 regs source destination index byte)
    (writeSuccess101f0Global global
      (writeSuccessMemcpyDestinationAddress destination index)
      (writeSuccess101e4Loaded byte)) obs6 after
    ltac:(unfold writeSuccessMemcpyByteRegs6, writeSuccess101f0Regs;
      rewrite lookup_insert; reflexivity)
    HcodeF4 HcodeD8 Hassume6 Hseg6) as (Hafter & Hobs6).
  subst obs0 obs1 obs2 obs3 obs4 obs5 obs6.
  subst after.
  exists (writeSuccess101d8Observations index length regs global),
    (writeSuccess101e0Observations (writeSuccessMemcpyByteRegs1 regs) global
      source index),
    (writeSuccess101e4Observations
      (writeSuccessMemcpyByteRegs2 regs source index) global mstatus2
      (writeSuccessMemcpySourceAddress source index) satp2 byte),
    (writeSuccess101e8Observations
      (writeSuccessMemcpyByteRegs3 regs source index byte) global
      destination index),
    (writeSuccess101ecObservations
      (writeSuccessMemcpyByteRegs4 regs source destination index byte) global index),
    (writeSuccess101f0Observations
      (writeSuccessMemcpyByteRegs5 regs source destination index byte) global
      mstatus5 (writeSuccessMemcpyDestinationAddress destination index) satp5
      (writeSuccess101e4Loaded byte) result),
    (writeSuccess101f4Observations
      (writeSuccessMemcpyByteRegs6 regs source destination index byte)
      (writeSuccess101f0Global global
        (writeSuccessMemcpyDestinationAddress destination index)
        (writeSuccess101e4Loaded byte))).
  split; first reflexivity.
  split; first reflexivity.
  split.
  - apply writeSuccessSegmentRecordsEmpty.
    unfold flattenMicroObservations.
    repeat rewrite writeSuccessConcatMicroLabelsApp.
    try rewrite Hlabels0. try rewrite Hlabels1. try rewrite Hlabels2.
    try rewrite Hlabels3. try rewrite Hlabels4. try rewrite Hlabels5.
    try rewrite Hlabels6. reflexivity.
  - split.
    + eapply (writeSuccessWithdrawalsSilentRecordedSnoc 0
        (writeSuccess101d8Before regs global, priorLog) []
        (writeSuccess101d8Before regs global, priorLog)
        (writeSuccess101d8Observations index length regs global)
        (writeSuccess101d8TakenAfter regs global)).
      * apply writeSuccessWithdrawalsRecordedRunZero.
      * exact Hseg0.
      * exact Hlabels0.
    + split.
      * eapply (writeSuccessWithdrawalsSilentRecordedSnoc 0
          (writeSuccessMemcpyByteState1 regs global, priorLog) []
          (writeSuccessMemcpyByteState1 regs global, priorLog)
          (writeSuccess101e0Observations (writeSuccessMemcpyByteRegs1 regs)
            global source index)
          (writeSuccessMemcpyByteState2 regs global source index)).
        -- apply writeSuccessWithdrawalsRecordedRunZero.
        -- exact Hseg1.
        -- exact Hlabels1.
      * split.
        -- eapply (writeSuccessWithdrawalsSilentRecordedSnoc 0
            (writeSuccessMemcpyByteState2 regs global source index, priorLog) []
            (writeSuccessMemcpyByteState2 regs global source index, priorLog)
            (writeSuccess101e4Observations
              (writeSuccessMemcpyByteRegs2 regs source index) global mstatus2
              (writeSuccessMemcpySourceAddress source index) satp2 byte)
            (writeSuccessMemcpyByteState3 regs global source index byte)).
           ++ apply writeSuccessWithdrawalsRecordedRunZero.
           ++ exact Hseg2.
           ++ exact Hlabels2.
        -- split.
           ++ eapply (writeSuccessWithdrawalsSilentRecordedSnoc 0
                (writeSuccessMemcpyByteState3 regs global source index byte,
                 priorLog) []
                (writeSuccessMemcpyByteState3 regs global source index byte,
                 priorLog)
                (writeSuccess101e8Observations
                  (writeSuccessMemcpyByteRegs3 regs source index byte) global
                  destination index)
                (writeSuccessMemcpyByteState4 regs global source destination
                  index byte)).
              ** apply writeSuccessWithdrawalsRecordedRunZero.
              ** exact Hseg3.
              ** exact Hlabels3.
           ++ split.
              ** eapply (writeSuccessWithdrawalsSilentRecordedSnoc 0
                   (writeSuccessMemcpyByteState4 regs global source destination
                     index byte, priorLog) []
                   (writeSuccessMemcpyByteState4 regs global source destination
                     index byte, priorLog)
                   (writeSuccess101ecObservations
                     (writeSuccessMemcpyByteRegs4 regs source destination index byte)
                     global index)
                   (writeSuccessMemcpyByteState5 regs global source destination
                     index byte)).
                 --- apply writeSuccessWithdrawalsRecordedRunZero.
                 --- exact Hseg4.
                 --- exact Hlabels4.
              ** split.
                 --- eapply (writeSuccessWithdrawalsSilentRecordedSnoc 0
                       (writeSuccessMemcpyByteState5 regs global source destination
                         index byte, priorLog) []
                       (writeSuccessMemcpyByteState5 regs global source destination
                         index byte, priorLog)
                       (writeSuccess101f0Observations
                         (writeSuccessMemcpyByteRegs5 regs source destination index byte)
                         global mstatus5
                         (writeSuccessMemcpyDestinationAddress destination index)
                         satp5 (writeSuccess101e4Loaded byte) result)
                       (writeSuccessMemcpyByteState6 regs global source destination
                         index byte)).
                     ++++ apply writeSuccessWithdrawalsRecordedRunZero.
                     ++++ exact Hseg5.
                     ++++ exact Hlabels5.
                 --- eapply (writeSuccessWithdrawalsSilentRecordedSnoc 0
                       (writeSuccessMemcpyByteState6 regs global source destination
                         index byte, priorLog) []
                       (writeSuccessMemcpyByteState6 regs global source destination
                         index byte, priorLog)
                       (writeSuccess101f4Observations
                         (writeSuccessMemcpyByteRegs6 regs source destination index byte)
                         (writeSuccess101f0Global global
                           (writeSuccessMemcpyDestinationAddress destination index)
                           (writeSuccess101e4Loaded byte)))
                       (writeSuccessMemcpyByteAfter regs global source destination
                         index byte)).
                     ++++ apply writeSuccessWithdrawalsRecordedRunZero.
                     ++++ exact Hseg6.
                     ++++ exact Hlabels6.
Qed.

Print Assumptions writeSuccessMemcpyBytePositionsExact.
