From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10194.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1019c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessStoreOutcome.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputRecordedPositions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionStateBuild.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankIndexed.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedEdgeEndpoint.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessWithdrawalsDirectOutputSelected state pc :
  In pc [0x10190; 0x10194; 0x10198; 0x1019c; 0x101a0] ->
  state.1.1.(seq_regs) !! "x1" =
    Some (RVal_Bits (Z_to_bv 64 0x156d0)) ->
  writeSuccessWithdrawalsSelectedOccurrence state pc = Some 2%nat.
Proof.
  intros Hpc Hx1.
  unfold writeSuccessWithdrawalsSelectedOccurrence,
    writeSuccessWithdrawalsRegisterUnsigned.
  cbn in Hpc.
  destruct Hpc as [Hpc|[Hpc|[Hpc|[Hpc|[Hpc|[]]]]]]; subst pc; cbn;
    rewrite Hx1; reflexivity.
Qed.

Theorem writeSuccessOutputRecordedPositionStates
    (regs : reg_map) (global : seq_global_state) (data size : bv 64)
    (returnTrace : isla_trace) priorLog segments after remaining :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10190)) ->
  regs !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156d0)) ->
  regs !! "x10" = Some (RVal_Bits data) ->
  regs !! "x11" = Some (RVal_Bits size) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156d0 = Some returnTrace ->
  writeSuccessWithdrawalsInstructionTable global ->
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  set_Forall (fun address =>
    ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
    (dom global.(seq_mem)) ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  WriteSuccessWithdrawalsRecordedRun 5
    (writeSuccess10190Before regs global, priorLog) segments after ->
  exists states,
    length states = 6%nat /\
    nth_error states 0 =
      Some (writeSuccess10190Before regs global, priorLog) /\
    nth_error states 5 = Some after /\
    WriteSuccessWithdrawalsPositionEdges segments states /\
    forall offset stateAt,
      (offset < 5)%nat ->
      nth_error states offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining (384 + offset) stateAt.
Proof.
  intros Hpc Hx1 Hx10 Hx11 Hreturn Htable Hfacts Hdom Hx9 Hrange Hrecorded.
  have Halign : bv_extract 0 2 (Z_to_bv 64 0x156d0) = BV 2 0 by
    (vm_compute; apply bv_eq; reflexivity).
  destruct (writeSuccessOutputRecordedPositionPath regs global data size
    (Z_to_bv 64 0x156d0) returnTrace priorLog segments after Hpc Hx1 Hx10 Hx11
    Halign Hreturn Htable Hfacts Hdom Hrecorded) as
    (mstatusBits & satp & result98 & result9c & states & Hsegments & Hafter &
     Hlength & Hstart & Hend & Hedges).
  exists states. repeat split; try assumption.
  intros offset stateAt Hoffset Hnth.
  destruct offset as [|[|[|[|[|offset]]]]]; try lia.
  - rewrite Hstart in Hnth. injection Hnth as <-.
    eapply (writeSuccessWithdrawalsPositionStateBuild remaining 384
      (writeSuccess10190Before regs global, priorLog) 0x10190); try lia;
      try reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc, writeSuccess10190Before,
        writeSuccess15694Local. cbn. rewrite Hpc. unfold bvn_unsigned. cbn.
      rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + apply writeSuccessWithdrawalsDirectOutputSelected.
      * cbn. tauto.
      * exact Hx1.
    + exact Hx9.
  - destruct stateAt as [stateMachine stateLog].
    destruct (writeSuccessWithdrawalsActualRecordedSuccessor segments states 0
      (writeSuccess10190Observations regs global) (stateMachine, stateLog)
      {| microLabels := []; microAfter := writeSuccess10190Before regs global |}
      Hedges ltac:(rewrite Hsegments; reflexivity) Hnth) as (labels & Hlast).
    unfold writeSuccess10190Observations in Hlast.
    rewrite writeSuccessWithdrawalsLastAppSingleton in Hlast.
    have Hmachine := f_equal microAfter Hlast. cbn in Hmachine. subst stateMachine.
    eapply (writeSuccessWithdrawalsPositionStateBuild remaining 385
      (writeSuccess10190After regs global, stateLog) 0x10194); try lia;
      try reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc, writeSuccess10190After,
        writeSuccess15694Local. cbn. rewrite lookup_insert.
      rewrite writeSuccess10190NextPcExact. unfold bvn_unsigned. cbn.
      rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + apply writeSuccessWithdrawalsDirectOutputSelected.
      * cbn. tauto.
      * unfold writeSuccess10190After, writeSuccess15694Local. cbn.
        rewrite writeSuccess10190RegsLookupOther; try discriminate. exact Hx1.
    + unfold writeSuccess10190After, writeSuccess15694Local. cbn.
      rewrite writeSuccess10190RegsLookupOther; try discriminate. exact Hx9.
  - destruct stateAt as [stateMachine stateLog].
    destruct (writeSuccessWithdrawalsActualRecordedSuccessor segments states 1
      (writeSuccess10194Observations (writeSuccessOutputRegs1 regs) global
        writeSuccess10190Link) (stateMachine, stateLog)
      {| microLabels := []; microAfter := writeSuccess10190Before regs global |}
      Hedges ltac:(rewrite Hsegments; reflexivity) Hnth) as (labels & Hlast).
    unfold writeSuccess10194Observations in Hlast.
    rewrite writeSuccessWithdrawalsLastAppSingleton in Hlast.
    have Hmachine := f_equal microAfter Hlast. cbn in Hmachine. subst stateMachine.
    eapply (writeSuccessWithdrawalsPositionStateBuild remaining 386
      (writeSuccess10194After (writeSuccessOutputRegs1 regs) global
        writeSuccess10190Link, stateLog) 0x10198); try lia; try reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc, writeSuccess10194After,
        writeSuccess10194Local. cbn. rewrite lookup_insert.
      rewrite writeSuccess10194NextPcExact. unfold bvn_unsigned. cbn.
      rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + apply writeSuccessWithdrawalsDirectOutputSelected.
      * cbn. tauto.
      * unfold writeSuccess10194After, writeSuccess10194Local. cbn.
        rewrite writeSuccess10194RegsLookupOther; try discriminate.
        unfold writeSuccessOutputRegs1. rewrite writeSuccess10190RegsLookupOther;
          try discriminate. exact Hx1.
    + unfold writeSuccess10194After, writeSuccess10194Local. cbn.
      rewrite writeSuccess10194RegsLookupOther; try discriminate.
      unfold writeSuccessOutputRegs1. rewrite writeSuccess10190RegsLookupOther;
        try discriminate. exact Hx9.
  - destruct stateAt as [stateMachine stateLog].
    destruct (writeSuccessWithdrawalsActualRecordedSuccessor segments states 2
      (writeSuccess10198Observations (writeSuccessOutputRegs2 regs) global
        mstatusBits writeSuccessOutputPortBase satp data result98
        WriteSuccessStoreMmio) (stateMachine, stateLog)
      {| microLabels := []; microAfter := writeSuccess10190Before regs global |}
      Hedges ltac:(rewrite Hsegments; reflexivity) Hnth) as (labels & Hlast).
    unfold writeSuccess10198Observations in Hlast.
    rewrite writeSuccessWithdrawalsLastAppSingleton in Hlast.
    have Hmachine := f_equal microAfter Hlast. cbn in Hmachine. subst stateMachine.
    eapply (writeSuccessWithdrawalsPositionStateBuild remaining 387
      (writeSuccess10198After (writeSuccessOutputRegs2 regs) global
        writeSuccessOutputPortBase data WriteSuccessStoreMmio, stateLog)
      0x1019c); try lia; try reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc, writeSuccess10198After,
        writeSuccess15694Local. cbn. rewrite lookup_insert.
      rewrite writeSuccess10198NextPcExact. unfold bvn_unsigned. cbn.
      rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + apply writeSuccessWithdrawalsDirectOutputSelected.
      * cbn. tauto.
      * unfold writeSuccess10198After, writeSuccess15694Local. cbn.
        rewrite writeSuccess10198RegsLookupOther; try discriminate.
        rewrite writeSuccessOutputRegs2LookupOther; try discriminate. exact Hx1.
    + unfold writeSuccess10198After, writeSuccess15694Local. cbn.
      rewrite writeSuccess10198RegsLookupOther; try discriminate.
      rewrite writeSuccessOutputRegs2LookupOther; try discriminate. exact Hx9.
  - destruct stateAt as [stateMachine stateLog].
    destruct (writeSuccessWithdrawalsActualRecordedSuccessor segments states 3
      (writeSuccess1019cObservations (writeSuccessOutputRegs3 regs) global
        mstatusBits writeSuccessOutputPortBase satp size result9c
        WriteSuccessStoreMmio) (stateMachine, stateLog)
      {| microLabels := []; microAfter := writeSuccess10190Before regs global |}
      Hedges ltac:(rewrite Hsegments; reflexivity) Hnth) as (labels & Hlast).
    unfold writeSuccess1019cObservations in Hlast.
    rewrite writeSuccessWithdrawalsLastAppSingleton in Hlast.
    have Hmachine := f_equal microAfter Hlast. cbn in Hmachine. subst stateMachine.
    eapply (writeSuccessWithdrawalsPositionStateBuild remaining 388
      (writeSuccess1019cAfter (writeSuccessOutputRegs3 regs) global
        writeSuccessOutputPortBase size WriteSuccessStoreMmio, stateLog)
      0x101a0); try lia; try reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc, writeSuccess1019cAfter,
        writeSuccess15694Local. cbn. rewrite lookup_insert.
      rewrite writeSuccess1019cNextPcExact. unfold bvn_unsigned. cbn.
      rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + apply writeSuccessWithdrawalsDirectOutputSelected.
      * cbn. tauto.
      * unfold writeSuccess1019cAfter, writeSuccess15694Local. cbn.
        rewrite writeSuccess1019cRegsLookupOther; try discriminate.
        rewrite writeSuccessOutputRegs3LookupOther; try discriminate. exact Hx1.
    + unfold writeSuccess1019cAfter, writeSuccess15694Local. cbn.
      rewrite writeSuccess1019cRegsLookupOther; try discriminate.
      rewrite writeSuccessOutputRegs3LookupOther; try discriminate. exact Hx9.
Qed.

Print Assumptions writeSuccessOutputRecordedPositionStates.
Print Assumptions writeSuccessWithdrawalsDirectOutputSelected.
