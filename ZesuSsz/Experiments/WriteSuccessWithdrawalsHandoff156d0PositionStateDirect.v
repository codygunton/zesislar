From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_94.a156d0.
Require Import IslaTraces.write_success_94.a156d4.
Require Import IslaTraces.write_success_94.a156d8.
Require Import IslaTraces.write_success_07.a15d10.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionStateBuild.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankIndexed.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedEdgeEndpoint.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedSilentPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.

Import ListNotations.
Open Scope Z_scope.

Theorem writeSuccessWithdrawals156d0RecordedPositionStatesDirect regs global
    (sp value : bv 64) priorLog (mstatusBits satp oldDest : bv 64)
    (oldX1 : valu) segments after remaining :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156d0)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "mstatus" =
    Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x10" = Some (RVal_Bits oldDest) ->
  regs !! "x1" = Some oldX1 ->
  writeSuccess156d0SysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156d0Aligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156d0Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156d0Upper = Some (Val_Bool true) ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess156d0Address sp)) 8 =
    Some (bv_to_bvn value) ->
  writeSuccessWithdrawalsInstructionTable global ->
  regs !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  WriteSuccessWithdrawalsRecordedRun 3
    (writeSuccess156d0Before regs global, priorLog) segments after ->
  exists states,
    length states = 4%nat /\
    nth_error states 0 =
      Some (writeSuccess156d0Before regs global, priorLog) /\
    nth_error states 1 =
      Some (writeSuccess156d0After regs global value, priorLog) /\
    nth_error states 2 =
      Some (writeSuccess156d4After (writeSuccess156d0Regs regs value) global,
        priorLog) /\
    nth_error states 3 = Some after /\
    WriteSuccessWithdrawalsPositionEdges segments states /\
    forall offset stateAt,
      (offset < 3)%nat ->
      nth_error states offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining (389 + offset) stateAt.
Proof.
  intros Hpc Hsp Hmstatus Hsatp Hdest Hx1 Hsys HmstatusAssume Haligned
    Hlower Hupper Hread Htable Hx9 Hrange Hrecorded.
  destruct (writeSuccessWithdrawalsRecordedRunPositionEdges 3
    (writeSuccess156d0Before regs global, priorLog) segments after Hrecorded) as
    (states & Hlength & Hstart & Hend & Hedges).
  have Hrun := proj1 Hrecorded.
  inversion Hrun as
    [|? ? observations0 middle0 segments0 machineAfter0 Hseg0 Hrun0]; subst.
  inversion Hrun0 as
    [|? ? observations1 middle1 segments1 machineAfter1 Hseg1 Hrun1]; subst.
  inversion Hrun1 as
    [|? ? observations2 middle2 segments2 machineAfter2 Hseg2 Hrun2]; subst.
  have Hcode0 := Htable 0x156d0 a156d0 ltac:(cbn; tauto).
  have Hcode1 := Htable 0x156d4 a156d4 ltac:(cbn; tauto).
  have Hcode2 := Htable 0x156d8 a156d8 ltac:(cbn; tauto).
  have Hcode3 := Htable 0x15d10 a15d10 ltac:(cbn; tauto).
  destruct (segment_156d0_covered regs global mstatusBits sp satp value oldDest
    observations0 middle0 Hpc Hsp Hmstatus Hsatp Hdest Hsys HmstatusAssume
    Haligned Hlower Hupper Hread Hcode0 Hcode1 Hseg0) as (Hmiddle0 & Hobs0).
  subst middle0 observations0.
  have Hpc1 : writeSuccess156d0Regs regs value !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x156d4)) by
    (unfold writeSuccess156d0Regs; rewrite lookup_insert;
      rewrite writeSuccess156d0NextPcExact; reflexivity).
  have Hx1_1 : writeSuccess156d0Regs regs value !! "x1" = Some oldX1 by
    (rewrite writeSuccess156d0RegsLookupOther; try discriminate; exact Hx1).
  have Hmstatus1 : eval_a_exp (writeSuccess156d0Regs regs value)
      writeSuccess15694Mstatus = Some (Val_Bool true).
  { unfold writeSuccess156d0Regs. cbn.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate. exact HmstatusAssume. }
  destruct (segment_156d4_mstatus_covered (writeSuccess156d0Regs regs value)
    global oldX1 observations1 middle1 Hpc1 Hx1_1 Hcode1 Hcode2 Hmstatus1
    Hseg1) as (Hmiddle1 & Hobs1).
  subst middle1 observations1.
  set (regs2 := writeSuccess156d4Regs (writeSuccess156d0Regs regs value)).
  have Hpc2 : regs2 !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156d8)) by
    (unfold regs2, writeSuccess156d4Regs; rewrite lookup_insert;
      rewrite writeSuccess156d4NextPcExact; reflexivity).
  have Hx1_2 : regs2 !! "x1" = Some (RVal_Bits writeSuccess156d8Ra).
  { unfold regs2, writeSuccess156d4Regs. rewrite lookup_insert_ne;
      last discriminate. rewrite lookup_insert. reflexivity. }
  have Hmstatus2 : eval_a_exp regs2 writeSuccess15694Mstatus =
      Some (Val_Bool true).
  { unfold regs2, writeSuccess156d4Regs. cbn.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate. exact Hmstatus1. }
  destruct (segment_156d8_mstatus_covered regs2 global observations2 middle2
    Hpc2 Hx1_2 Hcode2 Hcode3 Hmstatus2 Hseg2) as (Hmiddle2 & Hobs2).
  subst observations2.
  have Hsegments2 : segments2 = [] by (inversion Hrun2; reflexivity).
  subst segments2.
  have Hsilent0 : concat (map microLabels
      (writeSuccess156d0Observations regs global mstatusBits sp satp value)) = []
    by (unfold writeSuccess156d0Observations,
      writeSuccess156d0PrefixObservations, writeSuccess156d0PreReadObservations,
      writeSuccess156d0PostReadPrefix; reflexivity).
  have Hsilent1 : concat (map microLabels
      (writeSuccess156d4Observations (writeSuccess156d0Regs regs value) global))
      = [] by
    (unfold writeSuccess156d4Observations,
      writeSuccess156d4PrefixObservations; reflexivity).
  have Hstate1 : nth_error states 1 =
      Some (writeSuccess156d0After regs global value, priorLog).
  { destruct (nth_error states 1) as [[machine1 log1]|] eqn:Hnth1;
      last (rewrite nth_error_None in Hnth1; rewrite Hlength in Hnth1; lia).
    destruct (writeSuccessWithdrawalsActualRecordedSuccessor _ states 0
      (writeSuccess156d0Observations regs global mstatusBits sp satp value)
      (machine1, log1)
      {| microLabels := []; microAfter := writeSuccess156d0Before regs global |}
      Hedges ltac:(reflexivity) Hnth1) as (labels & Hlast).
    unfold writeSuccess156d0Observations in Hlast.
    rewrite writeSuccessWithdrawalsLastAppSingleton in Hlast.
    have Hmachine := f_equal microAfter Hlast. cbn in Hmachine. subst machine1.
    have Hlog := writeSuccessWithdrawalsActualSilentSuccessor _ states 0
      (writeSuccess156d0Observations regs global mstatusBits sp satp value)
      (writeSuccess156d0Before regs global, priorLog)
      (writeSuccess156d0After regs global value, log1) Hedges
      ltac:(reflexivity) Hstart Hnth1 Hsilent0.
    cbn in Hlog. subst log1. reflexivity. }
  have Hstate2 : nth_error states 2 =
      Some (writeSuccess156d4After (writeSuccess156d0Regs regs value) global,
        priorLog).
  { destruct (nth_error states 2) as [[machine2 log2]|] eqn:Hnth2;
      last (rewrite nth_error_None in Hnth2; rewrite Hlength in Hnth2; lia).
    destruct (writeSuccessWithdrawalsActualRecordedSuccessor _ states 1
      (writeSuccess156d4Observations (writeSuccess156d0Regs regs value) global)
      (machine2, log2)
      {| microLabels := []; microAfter := writeSuccess156d0Before regs global |}
      Hedges ltac:(reflexivity) Hnth2) as (labels & Hlast).
    unfold writeSuccess156d4Observations in Hlast.
    rewrite writeSuccessWithdrawalsLastAppSingleton in Hlast.
    have Hmachine := f_equal microAfter Hlast. cbn in Hmachine. subst machine2.
    have Hlog := writeSuccessWithdrawalsActualSilentSuccessor _ states 1
      (writeSuccess156d4Observations (writeSuccess156d0Regs regs value) global)
      (writeSuccess156d0After regs global value, priorLog)
      (writeSuccess156d4After (writeSuccess156d0Regs regs value) global, log2)
      Hedges ltac:(reflexivity) Hstate1 Hnth2 Hsilent1.
    cbn in Hlog. subst log2. reflexivity. }
  exists states. repeat split; try assumption.
  intros offset stateAt Hoffset Hnth.
  destruct offset as [|[|[|offset]]]; try lia.
  - rewrite Hstart in Hnth. injection Hnth as <-.
    eapply (writeSuccessWithdrawalsPositionStateBuild remaining 389
      (writeSuccess156d0Before regs global, priorLog) 0x156d0).
    + lia.
    + vm_compute. reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc, writeSuccess156d0Before,
        writeSuccess15694Local. cbn. rewrite Hpc. unfold bvn_unsigned. cbn.
      rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + unfold writeSuccessWithdrawalsSelectedOccurrence. vm_compute. reflexivity.
    + exact Hx9.
    + exact Hrange.
  - rewrite Hstate1 in Hnth. injection Hnth as <-.
    eapply (writeSuccessWithdrawalsPositionStateBuild remaining 390
      (writeSuccess156d0After regs global value, priorLog) 0x156d4).
    + lia.
    + vm_compute. reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc, writeSuccess156d0After,
        writeSuccess15694Local. cbn. rewrite lookup_insert.
      rewrite writeSuccess156d0NextPcExact. unfold bvn_unsigned. cbn.
      rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + unfold writeSuccessWithdrawalsSelectedOccurrence. vm_compute. reflexivity.
    + unfold writeSuccess156d0After, writeSuccess15694Local. cbn.
      rewrite writeSuccess156d0RegsLookupOther; try discriminate. exact Hx9.
    + exact Hrange.
  - rewrite Hstate2 in Hnth. injection Hnth as <-.
    eapply (writeSuccessWithdrawalsPositionStateBuild remaining 391
      (writeSuccess156d4After (writeSuccess156d0Regs regs value) global,
        priorLog) 0x156d8).
    + lia.
    + vm_compute. reflexivity.
    + unfold writeSuccessWithdrawalsConcretePc, writeSuccess156d4After,
        writeSuccess15694Local. cbn. rewrite lookup_insert.
      rewrite writeSuccess156d4NextPcExact. unfold bvn_unsigned. cbn.
      rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + unfold writeSuccessWithdrawalsSelectedOccurrence. vm_compute. reflexivity.
    + unfold writeSuccess156d4After, writeSuccess15694Local. cbn.
      rewrite writeSuccess156d4RegsLookupOther; try discriminate.
      rewrite writeSuccess156d0RegsLookupOther; try discriminate. exact Hx9.
    + exact Hrange.
Qed.

Print Assumptions writeSuccessWithdrawals156d0RecordedPositionStatesDirect.
