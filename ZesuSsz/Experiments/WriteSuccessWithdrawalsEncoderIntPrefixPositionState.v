From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntPositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntPrefixRecordedPositions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedEdgeEndpoint.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d1c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d20.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d24.

Import ListNotations.
Open Scope Z_scope.
Lemma writeSuccessWithdrawalsEncoderIntPrefixActualPositions remaining start
    (regs : reg_map) (global : seq_global_state) (value sp returnAddress : bv 64)
    scratch priorLog segments after :
  writeSuccessWithdrawalsEncoderIntPositionStart start returnAddress ->
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d10)) ->
  regs !! "x1" = Some (RVal_Bits returnAddress) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some (RVal_Bits value) ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  read_mem_list global.(seq_mem) (bv_unsigned sp - 16) 16%N = Some scratch ->
  islaMemoryRange (bv_unsigned sp - 16) 16 ->
  bv_unsigned sp `mod` 8 = 0 ->
  0x20000000 <= bv_unsigned sp - 16 ->
  bv_unsigned sp <= 0x40000000 ->
  writeSuccessWithdrawalsInstructionTable global ->
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  WriteSuccessWithdrawalsRecordedRun 7
    (writeSuccess15d10Before regs global, priorLog) segments after ->
  exists states,
    WriteSuccessWithdrawalsPositionEdges segments states /\
    forall offset stateAt,
      (offset < 7)%nat ->
      nth_error states offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining (start + offset) stateAt.
Proof.
  intros Hstart Hpc Hx1 Hx2 Hx10 Hx9 Hcounter Hread Hrange Halign Hlower
    Hupper Htable Hfacts Hrecorded.
  destruct (writeSuccessEncoderIntPrefixRecordedPositionPath regs global value
    sp returnAddress scratch priorLog segments after Hpc Hx1 Hx2 Hx10 Hread
    Hrange Halign Hlower Hupper Htable Hfacts Hrecorded) as
    (mstatus & satp & mstatus2 & satp2 & result14 & result18 & states &
     Hafter & Hsegments & Hlength & Hstate0 & Hstate7 & Hedges).
  exists states. split; first exact Hedges.
  intros offset stateAt Hoffset Hstate.
  destruct offset as [|offset].
  - rewrite Hstate0 in Hstate. injection Hstate as <-.
    eapply writeSuccessWithdrawalsEncoderIntActualPositionState with
      (returnAddress := returnAddress) (pc := 0x15d10).
    + exact Hstart.
    + lia.
    + reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc, writeSuccess15d10Before.
      unfold writeSuccess15d10Local. cbn. rewrite Hpc. reflexivity.
    + eapply writeSuccessWithdrawalsEncoderIntegerSelected; first (cbn; auto).
      exact Hx1.
    + exact Hx9.
    + exact Hcounter.
  - destruct offset as [|offset].
    + have Hobs : nth_error segments 0 =
        Some (writeSuccess15d10Observations regs global sp).
    { rewrite Hsegments. reflexivity. }
    destruct (writeSuccessWithdrawalsActualRecordedSuccessor segments states 0
      (writeSuccess15d10Observations regs global sp) stateAt
      {| microLabels := []; microAfter := stateAt.1 |} Hedges Hobs Hstate) as
      (labels & Hlast).
    have Hmachine := f_equal microAfter Hlast.
    cbn [writeSuccess15d10Observations writeSuccess15d10PrefixObservations
      writeSuccess15d10Observation] in Hmachine.
    destruct stateAt as [machine log]. cbn in Hmachine |- *. subst machine.
    eapply writeSuccessWithdrawalsEncoderIntActualPositionState with
      (returnAddress := returnAddress) (pc := 0x15d14).
    * exact Hstart.
    * lia.
    * reflexivity.
    * unfold writeSuccessWithdrawalsConcretePc, writeSuccess15d10After,
        writeSuccess15d10Local. cbn. rewrite lookup_insert.
      rewrite writeSuccess15d10NextPcExact.
      unfold bvn_unsigned. cbn. rewrite Z_to_bv_unsigned. reflexivity.
    * eapply writeSuccessWithdrawalsEncoderIntegerSelected; first (cbn; auto).
      unfold writeSuccess15d10After, writeSuccess15d10Local. cbn.
      rewrite writeSuccess15d10RegsLookupOther; try discriminate. exact Hx1.
    * unfold writeSuccess15d10After, writeSuccess15d10Local. cbn.
      rewrite writeSuccess15d10RegsLookupOther; try discriminate. exact Hx9.
    * exact Hcounter.
    + destruct offset as [|offset].
      * have Hobs : nth_error segments 1 = Some
          (writeSuccess15d14Observations
            (writeSuccessEncoderIntRegs1 regs sp) global mstatus
            (sp - BV 64 16)%bv satp returnAddress result14).
        { rewrite Hsegments. reflexivity. }
        destruct (writeSuccessWithdrawalsActualRecordedSuccessor segments states
          1 _ stateAt {| microLabels := []; microAfter := stateAt.1 |}
          Hedges Hobs Hstate) as (labels & Hlast).
        have Hmachine := f_equal microAfter Hlast.
        cbn [writeSuccess15d14Observations writeSuccess15d14PrefixObservations]
          in Hmachine.
        destruct stateAt as [machine log]. cbn in Hmachine |- *. subst machine.
        eapply writeSuccessWithdrawalsEncoderIntActualPositionState with
          (returnAddress := returnAddress) (pc := 0x15d18).
        -- exact Hstart.
        -- lia.
        -- reflexivity.
        -- unfold writeSuccessWithdrawalsConcretePc, writeSuccess15d14After,
             writeSuccess15694Local. cbn. rewrite lookup_insert. reflexivity.
        -- apply writeSuccessWithdrawalsEncoderIntegerSelected.
           ++ cbn; tauto.
           ++ unfold writeSuccessEncoderIntRegs2,
                writeSuccessEncoderIntRegs1.
              rewrite writeSuccess15d14RegsLookupOther; try discriminate.
              rewrite writeSuccess15d10RegsLookupOther; try discriminate.
              exact Hx1.
        -- unfold writeSuccessEncoderIntRegs2, writeSuccessEncoderIntRegs1.
           rewrite writeSuccess15d14RegsLookupOther; try discriminate.
           rewrite writeSuccess15d10RegsLookupOther; try discriminate.
           exact Hx9.
        -- exact Hcounter.
      * destruct offset as [|offset].
        -- have Hobs : nth_error segments 2 = Some
             (writeSuccess15d18Observations
               (writeSuccessEncoderIntRegs2 regs sp)
               (writeSuccessEncoderIntGlobal1 global sp returnAddress)
               mstatus2 (sp - BV 64 16)%bv satp2 value result18).
           { rewrite Hsegments. reflexivity. }
           destruct (writeSuccessWithdrawalsActualRecordedSuccessor segments states
             2 _ stateAt {| microLabels := []; microAfter := stateAt.1 |}
             Hedges Hobs Hstate) as (labels & Hlast).
           have Hmachine := f_equal microAfter Hlast.
           cbn [writeSuccess15d18Observations writeSuccess15d18PrefixObservations]
             in Hmachine.
           destruct stateAt as [machine log]. cbn in Hmachine |- *. subst machine.
           eapply writeSuccessWithdrawalsEncoderIntActualPositionState with
             (returnAddress := returnAddress) (pc := 0x15d1c).
           ++ exact Hstart.
           ++ lia.
           ++ reflexivity.
           ++ unfold writeSuccessWithdrawalsConcretePc, writeSuccess15d18After,
                writeSuccess15694Local. cbn. rewrite lookup_insert. reflexivity.
           ++ apply writeSuccessWithdrawalsEncoderIntegerSelected.
              ** cbn; tauto.
              ** unfold writeSuccessEncoderIntRegs3,
                   writeSuccessEncoderIntRegs2, writeSuccessEncoderIntRegs1.
                 rewrite writeSuccess15d18RegsLookupOther; try discriminate.
                 rewrite writeSuccess15d14RegsLookupOther; try discriminate.
                 rewrite writeSuccess15d10RegsLookupOther; try discriminate.
                 exact Hx1.
           ++ unfold writeSuccessEncoderIntRegs3,
                writeSuccessEncoderIntRegs2, writeSuccessEncoderIntRegs1.
              rewrite writeSuccess15d18RegsLookupOther; try discriminate.
              rewrite writeSuccess15d14RegsLookupOther; try discriminate.
              rewrite writeSuccess15d10RegsLookupOther; try discriminate.
              exact Hx9.
           ++ exact Hcounter.
        -- destruct offset as [|offset].
           ++ have Hobs : nth_error segments 3 = Some
                (writeSuccess15d1cObservations
                  (writeSuccessEncoderIntRegs3 regs sp)
                  (writeSuccessEncoderIntGlobal2 global sp returnAddress value)
                  (sp - BV 64 16)%bv).
              { rewrite Hsegments. reflexivity. }
              destruct (writeSuccessWithdrawalsActualRecordedSuccessor segments states
                3 _ stateAt {| microLabels := []; microAfter := stateAt.1 |}
                Hedges Hobs Hstate) as (labels & Hlast).
              have Hmachine := f_equal microAfter Hlast.
              cbn [writeSuccess15d1cObservations
                writeSuccess15d1cPrefixObservations] in Hmachine.
              destruct stateAt as [machine log]. cbn in Hmachine |- *. subst machine.
              eapply writeSuccessWithdrawalsEncoderIntActualPositionState with
                (returnAddress := returnAddress) (pc := 0x15d20).
              ** exact Hstart.
              ** lia.
              ** reflexivity.
              ** unfold writeSuccessWithdrawalsConcretePc,
                   writeSuccess15d1cAfter, writeSuccess15d1cLocal.
                 cbn. rewrite lookup_insert. reflexivity.
              ** apply writeSuccessWithdrawalsEncoderIntegerSelected.
                 --- cbn; tauto.
                 --- unfold writeSuccessEncoderIntRegs4,
                      writeSuccessEncoderIntRegs3, writeSuccessEncoderIntRegs2,
                      writeSuccessEncoderIntRegs1.
                     rewrite writeSuccess15d1cRegsLookupOther; try discriminate.
                     rewrite writeSuccess15d18RegsLookupOther; try discriminate.
                     rewrite writeSuccess15d14RegsLookupOther; try discriminate.
                     rewrite writeSuccess15d10RegsLookupOther; try discriminate.
                     exact Hx1.
              ** unfold writeSuccessEncoderIntRegs4,
                   writeSuccessEncoderIntRegs3, writeSuccessEncoderIntRegs2,
                   writeSuccessEncoderIntRegs1.
                 rewrite writeSuccess15d1cRegsLookupOther; try discriminate.
                 rewrite writeSuccess15d18RegsLookupOther; try discriminate.
                 rewrite writeSuccess15d14RegsLookupOther; try discriminate.
                 rewrite writeSuccess15d10RegsLookupOther; try discriminate.
                 exact Hx9.
              ** exact Hcounter.
           ++ destruct offset as [|offset].
              ** have Hobs : nth_error segments 4 = Some
                   (writeSuccess15d20Observations
                     (writeSuccessEncoderIntRegs4 regs sp)
                     (writeSuccessEncoderIntGlobal2 global sp returnAddress value)).
                 { rewrite Hsegments. reflexivity. }
                 destruct (writeSuccessWithdrawalsActualRecordedSuccessor segments states
                   4 _ stateAt {| microLabels := []; microAfter := stateAt.1 |}
                   Hedges Hobs Hstate) as (labels & Hlast).
                 have Hmachine := f_equal microAfter Hlast.
                 cbn [writeSuccess15d20Observations
                   writeSuccess15d20PrefixObservations] in Hmachine.
                 destruct stateAt as [machine log]. cbn in Hmachine |- *. subst machine.
                 eapply writeSuccessWithdrawalsEncoderIntActualPositionState with
                   (returnAddress := returnAddress) (pc := 0x15d24).
                 --- exact Hstart.
                 --- lia.
                 --- reflexivity.
                 --- unfold writeSuccessWithdrawalsConcretePc,
                      writeSuccess15d20After, writeSuccess15694Local.
                     cbn. rewrite lookup_insert. reflexivity.
                 --- apply writeSuccessWithdrawalsEncoderIntegerSelected.
                     +++ cbn; tauto.
                     +++ unfold writeSuccessEncoderIntRegs5,
                          writeSuccessEncoderIntRegs4,
                          writeSuccessEncoderIntRegs3,
                          writeSuccessEncoderIntRegs2,
                          writeSuccessEncoderIntRegs1.
                         rewrite writeSuccess15d20RegsLookupOther; try discriminate.
                         rewrite writeSuccess15d1cRegsLookupOther; try discriminate.
                         rewrite writeSuccess15d18RegsLookupOther; try discriminate.
                         rewrite writeSuccess15d14RegsLookupOther; try discriminate.
                         rewrite writeSuccess15d10RegsLookupOther; try discriminate.
                         exact Hx1.
                 --- unfold writeSuccessEncoderIntRegs5,
                      writeSuccessEncoderIntRegs4, writeSuccessEncoderIntRegs3,
                      writeSuccessEncoderIntRegs2, writeSuccessEncoderIntRegs1.
                     rewrite writeSuccess15d20RegsLookupOther; try discriminate.
                     rewrite writeSuccess15d1cRegsLookupOther; try discriminate.
                     rewrite writeSuccess15d18RegsLookupOther; try discriminate.
                     rewrite writeSuccess15d14RegsLookupOther; try discriminate.
                     rewrite writeSuccess15d10RegsLookupOther; try discriminate.
                     exact Hx9.
                 --- exact Hcounter.
              ** destruct offset as [|offset].
                 --- have Hobs : nth_error segments 5 = Some
                      (writeSuccess15d24Observations
                        (writeSuccessEncoderIntRegs5 regs sp)
                        (writeSuccessEncoderIntGlobal2 global sp returnAddress value)).
                     { rewrite Hsegments. reflexivity. }
                     destruct (writeSuccessWithdrawalsActualRecordedSuccessor segments states
                       5 _ stateAt {| microLabels := []; microAfter := stateAt.1 |}
                       Hedges Hobs Hstate) as (labels & Hlast).
                     have Hmachine := f_equal microAfter Hlast.
                     cbn [writeSuccess15d24Observations
                       writeSuccess15d24PrefixObservations] in Hmachine.
                     destruct stateAt as [machine log]. cbn in Hmachine |- *.
                     subst machine.
                     eapply writeSuccessWithdrawalsEncoderIntActualPositionState with
                       (returnAddress := returnAddress) (pc := 0x15d28).
                     +++ exact Hstart.
                     +++ lia.
                     +++ reflexivity.
                     +++ unfold writeSuccessWithdrawalsConcretePc,
                          writeSuccess15d24After, writeSuccess15694Local.
                         cbn. rewrite lookup_insert. reflexivity.
                     +++ apply writeSuccessWithdrawalsEncoderIntegerSavedSelected.
                         *** tauto.
                         *** unfold writeSuccessWithdrawalsSavedReturn,
                              writeSuccessWithdrawalsRegisterUnsigned.
                             cbn.
                             unfold writeSuccessEncoderIntRegs6,
                               writeSuccessEncoderIntRegs5,
                               writeSuccessEncoderIntRegs4,
                               writeSuccessEncoderIntRegs3,
                               writeSuccessEncoderIntRegs2,
                               writeSuccessEncoderIntRegs1.
                             rewrite writeSuccess15d24RegsLookupOther; try discriminate.
                             rewrite writeSuccess15d20RegsLookupOther; try discriminate.
                             rewrite writeSuccess15d1cRegsLookupOther; try discriminate.
                             rewrite writeSuccess15d18RegsLookupOther; try discriminate.
                             rewrite writeSuccess15d14RegsLookupOther; try discriminate.
                             unfold writeSuccess15d10Regs.
                             rewrite lookup_insert_ne; last discriminate.
                             rewrite lookup_insert.
                             rewrite writeSuccessEncoderIntStackExact.
                             unfold bvn_unsigned.
                             rewrite (writeSuccessEncoderIntStackUnsigned sp Hrange).
                             replace (bv_unsigned sp - 16 + 8) with
                               (bv_unsigned sp - 8) by lia.
                             rewrite (writeSuccessEncoderIntAfterStoresRead global sp
                               returnAddress value Hrange).
                             reflexivity.
                     +++ unfold writeSuccessEncoderIntRegs6,
                          writeSuccessEncoderIntRegs5,
                          writeSuccessEncoderIntRegs4,
                          writeSuccessEncoderIntRegs3,
                          writeSuccessEncoderIntRegs2,
                          writeSuccessEncoderIntRegs1.
                         rewrite writeSuccess15d24RegsLookupOther; try discriminate.
                         rewrite writeSuccess15d20RegsLookupOther; try discriminate.
                         rewrite writeSuccess15d1cRegsLookupOther; try discriminate.
                         rewrite writeSuccess15d18RegsLookupOther; try discriminate.
                         rewrite writeSuccess15d14RegsLookupOther; try discriminate.
                         rewrite writeSuccess15d10RegsLookupOther; try discriminate.
                         exact Hx9.
                     +++ exact Hcounter.
                 --- lia.
Qed.

Print Assumptions writeSuccessWithdrawalsEncoderIntPrefixActualPositions.

