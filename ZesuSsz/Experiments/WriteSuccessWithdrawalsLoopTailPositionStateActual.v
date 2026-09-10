From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156dc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e0.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalAmountRead.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156dcLoopTailRecordedPositions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIteration410Context.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationBounds.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsLoopTailPositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOutputEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedEdgeEndpoint.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.
Open Scope Z_scope.

Theorem writeSuccessWithdrawalsLoopTailActualPositionStates args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    regs1 global1 regs2 global2 outputRegs outputGlobal finalRegs finalGlobal
    tailLog segments after :
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
      withdrawal).2 (sp + BV 64 1768)%bv =
    writeSuccess10190Before outputRegs outputGlobal ->
  writeSuccess156d8After
    (writeSuccess156d4Regs
      (writeSuccess156d0Regs
        (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0))
        (writeSuccessWithdrawalsAmountValue withdrawal))) outputGlobal =
    writeSuccess15d10Before finalRegs finalGlobal ->
  WriteSuccessWithdrawalsRecordedRun 3
    (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
       (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal),
     tailLog) segments after ->
  exists states,
    length states = 4%nat /\
    nth_error states 0 =
      Some
        (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
           (Z_to_bv 64 0x156dc)
           (writeSuccessWithdrawalsAmountValue withdrawal), tailLog) /\
    nth_error states 3 = Some after /\
    WriteSuccessWithdrawalsPositionEdges segments states /\
    (forall stateAt,
      nth_error states 0 = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining 407 stateAt) /\
    (forall stateAt,
      nth_error states 1 = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining 408 stateAt) /\
    (forall stateAt,
      nth_error states 2 = Some stateAt ->
      writeSuccessWithdrawalsTerminalPositionState remaining stateAt) /\
    (forall stateAt,
      nth_error states 3 = Some stateAt ->
      writeSuccessWithdrawalsConcretePc stateAt =
        Some (if remaining is O then 0x156e8 else 0x15694) /\
      stateAt.1.1.(seq_regs) !! "x9" =
        Some (RVal_Bits (Z_to_bv 64 (Z.of_nat remaining)))).
Proof.
  intros Hinv Hprefix Hentry1 Hentry2 Houtput HfinalEntry Hrecorded.
  destruct (writeSuccessWithdrawals407EndpointTailFacts args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 outputRegs outputGlobal finalRegs finalGlobal Hinv
    Hprefix Hentry1 Hentry2 Houtput HfinalEntry) as
    (Hstart & Hpc & Hx8 & Hx9 & Hmstatus & Htable).
  have HrangeS : (Z.of_nat (S remaining) < 2 ^ 64)%Z.
  { have H := writeSuccessWithdrawalsIterationRemainingRange args sp pointer
      base total processed (S remaining) withdrawal allBytes prefix current
      suffix scratch encoderScratch registerFrame memoryFrame priorLog state
      Hinv. lia. }
  have Hrange : (Z.of_nat remaining < 2 ^ 64)%Z by lia.
  have Hrecorded' : WriteSuccessWithdrawalsRecordedRun 3
      (writeSuccess156dcBefore
        (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
          (Z_to_bv 64 0x156dc)
          (writeSuccessWithdrawalsAmountValue withdrawal)).1.(seq_regs)
        (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
          (Z_to_bv 64 0x156dc)
          (writeSuccessWithdrawalsAmountValue withdrawal)).2,
       tailLog) segments after.
  { rewrite <- Hstart. exact Hrecorded. }
  destruct (writeSuccessWithdrawals156dcLoopTailRecordedPositionPath
    (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
      (Z_to_bv 64 0x156dc)
      (writeSuccessWithdrawalsAmountValue withdrawal)).1.(seq_regs)
    (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
      (Z_to_bv 64 0x156dc)
      (writeSuccessWithdrawalsAmountValue withdrawal)).2 pointer remaining
    tailLog segments after Hpc Hx8 Hx9 Hmstatus Htable Hrecorded') as
    (Hafter & Hsegments & states & Hlength & Hstate0 & Hstate3 & Hedges).
  exists states. split; first exact Hlength.
  split.
  - rewrite <- Hstart in Hstate0. exact Hstate0.
  - split; first exact Hstate3.
    split; first exact Hedges.
    split.
    + intros stateAt Hnth. rewrite Hstate0 in Hnth. injection Hnth as <-.
      eapply writeSuccessWithdrawalsTailPosition407; eassumption.
    + split.
      * intros stateAt1 Hnth.
    have Hobs : nth_error segments 0 = Some
        (writeSuccess156dcObservations
          (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
            (Z_to_bv 64 0x156dc)
            (writeSuccessWithdrawalsAmountValue withdrawal)).1.(seq_regs)
          (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
            (Z_to_bv 64 0x156dc)
            (writeSuccessWithdrawalsAmountValue withdrawal)).2 pointer) by
      (rewrite Hsegments; reflexivity).
        destruct (writeSuccessWithdrawalsActualRecordedSuccessor segments states
          0 _ stateAt1 {| microLabels := []; microAfter := stateAt1.1 |}
          Hedges Hobs Hnth) as (labels & Hlast).
        have Hmachine := f_equal microAfter Hlast.
        cbn [writeSuccess156dcObservations writeSuccess156dcPrefixObservations]
          in Hmachine.
        destruct stateAt1 as [machine log]. cbn in Hmachine |- *. subst machine.
        eapply writeSuccessWithdrawalsTailPosition408; eassumption.
      * split.
        -- intros stateAt2 Hnth.
        have Hobs : nth_error segments 1 = Some
        (writeSuccess156e0Observations
          (writeSuccess156dcRegs
            (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
              (Z_to_bv 64 0x156dc)
              (writeSuccessWithdrawalsAmountValue withdrawal)).1.(seq_regs)
            pointer)
          (writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
            (Z_to_bv 64 0x156dc)
            (writeSuccessWithdrawalsAmountValue withdrawal)).2
          (Z_to_bv 64 (Z.of_nat (S remaining)))) by
          (rewrite Hsegments; reflexivity).
          destruct (writeSuccessWithdrawalsActualRecordedSuccessor segments states
            1 _ stateAt2 {| microLabels := []; microAfter := stateAt2.1 |}
            Hedges Hobs Hnth) as (labels & Hlast).
          have Hmachine := f_equal microAfter Hlast.
          cbn [writeSuccess156e0Observations writeSuccess156e0PrefixObservations]
            in Hmachine.
          destruct stateAt2 as [machine log]. cbn in Hmachine |- *. subst machine.
          eapply writeSuccessWithdrawalsTailPosition409; eassumption.
        -- intros stateAt3 Hnth. rewrite Hstate3 in Hnth. injection Hnth as <-.
           rewrite Hafter. eapply writeSuccessWithdrawalsTailPosition410.
           exact Hrange.
Qed.

Print Assumptions writeSuccessWithdrawalsLoopTailActualPositionStates.
