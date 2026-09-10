From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntPositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntOutputPositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSuffixRecordedPositions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSuffix.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedEdgeEndpoint.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d30.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d34.

Import ListNotations.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsEncoderIntSuffixActualPositions remaining start
    (regs : reg_map) (global : seq_global_state) (sp returnAddress : bv 64)
    (returnTrace : isla_trace) priorLog segments after :
  writeSuccessWithdrawalsEncoderIntPositionStart start returnAddress ->
  regs !! "x2" = Some (RVal_Bits (sp - BV 64 16)%bv) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess15d28Link) ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  read_mem global.(seq_mem) (bv_unsigned sp - 8) 8%N =
    Some (bv_to_bvn returnAddress) ->
  islaMemoryRange (bv_unsigned sp - 16) 16 ->
  bv_unsigned sp `mod` 8 = 0 ->
  0x20000000 <= bv_unsigned sp - 16 ->
  bv_unsigned sp <= 0x40000000 ->
  bv_extract 0 2 returnAddress = BV 2 0 ->
  global.(seq_instrs) !! returnAddress = Some returnTrace ->
  writeSuccessWithdrawalsInstructionTable global ->
  WriteSuccessWithdrawalsRecordedRun 3
    (writeSuccess15d2cBefore (writeSuccessEncoderIntAfterOutputRegs regs) global,
      priorLog) segments after ->
  exists states,
    WriteSuccessWithdrawalsPositionEdges segments states /\
    forall offset stateAt,
      (offset < 3)%nat ->
      nth_error states offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining
        (start + (12 + offset))%nat stateAt.
Proof.
  intros Hstart Hx2 Hx1 Hx9 Hcounter Hfacts Hread Hrange Halign Hlower
    Hupper HreturnAlign Hreturn Htable Hrecorded.
  destruct (writeSuccessEncoderIntSuffixRecordedPositionPath regs global sp
    returnAddress returnTrace priorLog segments after Hx2 Hx1 Hfacts Hread
    Hrange Halign Hlower Hupper HreturnAlign Hreturn Htable Hrecorded) as
    (mstatus & satp & states & Hafter & Hsegments & Hlength & Hstate0 &
     Hstate3 & Hedges).
  exists states. split; first exact Hedges.
  intros offset stateAt Hoffset Hstate.
  destruct offset as [|offset].
  - rewrite Hstate0 in Hstate. injection Hstate as <-.
    eapply writeSuccessWithdrawalsEncoderIntActualPositionState with
      (returnAddress := returnAddress) (offset := 12%nat) (pc := 0x15d2c).
    + exact Hstart.
    + lia.
    + reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc, writeSuccess15d2cBefore.
      cbn. rewrite lookup_insert. reflexivity.
    + apply writeSuccessWithdrawalsEncoderIntegerSavedSelected.
      * tauto.
      * eapply writeSuccessWithdrawalsEncoderOutputSavedReturn.
        -- rewrite writeSuccessEncoderIntAfterOutputLookupOther; try discriminate.
           exact Hx2.
        -- exact Hread.
        -- exact Hrange.
    + rewrite writeSuccessEncoderIntAfterOutputLookupOther; try discriminate.
      exact Hx9.
    + exact Hcounter.
  - destruct offset as [|offset].
    + have Hobs : nth_error segments 0 = Some
        (writeSuccess15d2cObservations
          (writeSuccessEncoderIntAfterOutputRegs regs) global mstatus
          (sp - BV 64 16)%bv satp returnAddress).
      { rewrite Hsegments. reflexivity. }
      destruct (writeSuccessWithdrawalsActualRecordedSuccessor segments states 0
        _ stateAt {| microLabels := []; microAfter := stateAt.1 |}
        Hedges Hobs Hstate) as (labels & Hlast).
      have Hmachine := f_equal microAfter Hlast.
      cbn [writeSuccess15d2cObservations writeSuccess15d2cPrefixObservations]
        in Hmachine.
      destruct stateAt as [machine log]. cbn in Hmachine |- *. subst machine.
      eapply writeSuccessWithdrawalsEncoderIntActualPositionState with
        (returnAddress := returnAddress) (offset := 13%nat) (pc := 0x15d30).
      * exact Hstart.
      * lia.
      * reflexivity.
      * unfold writeSuccessWithdrawalsConcretePc, writeSuccess15d2cAfter,
          writeSuccess15694Local. cbn. rewrite lookup_insert. reflexivity.
      * apply writeSuccessWithdrawalsEncoderIntegerSelected.
        -- cbn; tauto.
        -- unfold writeSuccess15d2cRegs. rewrite lookup_insert_ne;
             last discriminate. rewrite lookup_insert. reflexivity.
      * unfold writeSuccess15d2cRegs. rewrite lookup_insert_ne; last discriminate.
        rewrite lookup_insert_ne; last discriminate.
        rewrite writeSuccessEncoderIntAfterOutputLookupOther; try discriminate.
        exact Hx9.
      * exact Hcounter.
    + destruct offset as [|offset].
      * have Hobs : nth_error segments 1 = Some
          (writeSuccess15d30Observations
            (writeSuccess15d2cRegs (writeSuccessEncoderIntAfterOutputRegs regs)
              returnAddress) global (sp - BV 64 16)%bv).
        { rewrite Hsegments. reflexivity. }
        destruct (writeSuccessWithdrawalsActualRecordedSuccessor segments states 1
          _ stateAt {| microLabels := []; microAfter := stateAt.1 |}
          Hedges Hobs Hstate) as (labels & Hlast).
        have Hmachine := f_equal microAfter Hlast.
        cbn [writeSuccess15d30Observations writeSuccess15d30PrefixObservations]
          in Hmachine.
        destruct stateAt as [machine log]. cbn in Hmachine |- *. subst machine.
        eapply writeSuccessWithdrawalsEncoderIntActualPositionState with
          (returnAddress := returnAddress) (offset := 14%nat) (pc := 0x15d34).
        -- exact Hstart.
        -- lia.
        -- reflexivity.
        -- unfold writeSuccessWithdrawalsConcretePc, writeSuccess15d30After,
             writeSuccess15694Local. cbn. rewrite lookup_insert. reflexivity.
        -- apply writeSuccessWithdrawalsEncoderIntegerSelected.
           ++ cbn; tauto.
           ++ rewrite writeSuccess15d30RegsLookupOther; try discriminate.
              unfold writeSuccess15d2cRegs.
              rewrite lookup_insert_ne; last discriminate.
              rewrite lookup_insert. reflexivity.
        -- rewrite writeSuccess15d30RegsLookupOther; try discriminate.
           unfold writeSuccess15d2cRegs.
           rewrite lookup_insert_ne; last discriminate.
           rewrite lookup_insert_ne; last discriminate.
           rewrite writeSuccessEncoderIntAfterOutputLookupOther; try discriminate.
           exact Hx9.
        -- exact Hcounter.
      * lia.
Qed.

Print Assumptions writeSuccessWithdrawalsEncoderIntSuffixActualPositions.
