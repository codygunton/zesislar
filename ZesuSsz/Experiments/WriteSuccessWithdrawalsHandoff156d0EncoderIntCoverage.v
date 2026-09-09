From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_94.a156d0.
Require Import IslaTraces.write_success_94.a156d4.
Require Import IslaTraces.write_success_94.a156d8.
Require Import IslaTraces.write_success_07.a15d10.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156d0EncoderIntRecorded.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Lemma writeSuccessWithdrawals156d0EncoderIntCoveredDirect regs global
    (sp value : bv 64) priorLog (mstatusBits satp oldDest : bv 64)
    (oldX1 : valu) segments after :
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
  WriteSuccessWithdrawalsRecordedRun 3
    (writeSuccess156d0Before regs global, priorLog) segments after ->
  after =
    (writeSuccess156d8After
      (writeSuccess156d4Regs (writeSuccess156d0Regs regs value)) global,
     priorLog).
Proof.
  intros Hpc Hsp Hmstatus Hsatp Hdest Hx1 Hsys HmstatusAssume Haligned
    Hlower Hupper Hread Htable Hrecorded.
  have Hcodeb4 := Htable 0x156d0 a156d0 ltac:(cbn; tauto).
  have Hcodeb8 := Htable 0x156d4 a156d4 ltac:(cbn; tauto).
  have Hcodebc := Htable 0x156d8 a156d8 ltac:(cbn; tauto).
  have HcodeInt := Htable 0x15d10 a15d10 ltac:(cbn; tauto).
  destruct Hrecorded as (Hrun & Hlog).
  inversion Hrun as
    [|? ? observations0 middle0 segments0 machineAfter0 Hseg0 Hrun0]; subst.
  inversion Hrun0 as
    [|? ? observations1 middle1 segments1 machineAfter1 Hseg1 Hrun1]; subst.
  inversion Hrun1 as
    [|? ? observations2 middle2 segments2 machineAfter2 Hseg2 Hrun2]; subst.
  destruct (segment_156d0_covered regs global mstatusBits sp satp value oldDest
    observations0 middle0 Hpc Hsp Hmstatus Hsatp Hdest Hsys HmstatusAssume
    Haligned Hlower Hupper Hread Hcodeb4 Hcodeb8 Hseg0) as (Hmiddle0 & Hobs0).
  subst middle0 observations0.
  have Hpc1 : writeSuccess156d0Regs regs value !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x156d4)).
  { unfold writeSuccess156d0Regs. rewrite lookup_insert.
    rewrite writeSuccess156d0NextPcExact. reflexivity. }
  have Hx1_1 : writeSuccess156d0Regs regs value !! "x1" = Some oldX1.
  { rewrite writeSuccess156d0RegsLookupOther; try discriminate. exact Hx1. }
  have Hmstatus1 : eval_a_exp (writeSuccess156d0Regs regs value)
      writeSuccess15694Mstatus = Some (Val_Bool true).
  { unfold writeSuccess156d0Regs. cbn.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate. exact HmstatusAssume. }
  destruct (segment_156d4_mstatus_covered (writeSuccess156d0Regs regs value)
    global oldX1 observations1 middle1 Hpc1 Hx1_1 Hcodeb8 Hcodebc Hmstatus1
    Hseg1) as (Hmiddle1 & Hobs1).
  subst middle1 observations1.
  set (r2 := writeSuccess156d4Regs (writeSuccess156d0Regs regs value)).
  have Hpc2 : r2 !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156d8)).
  { unfold r2, writeSuccess156d4Regs. rewrite lookup_insert.
    rewrite writeSuccess156d4NextPcExact. reflexivity. }
  have Hx1_2 : r2 !! "x1" = Some (RVal_Bits writeSuccess156d8Ra).
  { unfold r2, writeSuccess156d4Regs. rewrite lookup_insert_ne;
      last discriminate. rewrite lookup_insert. reflexivity. }
  have Hmstatus2 : eval_a_exp r2 writeSuccess15694Mstatus =
      Some (Val_Bool true).
  { unfold r2, writeSuccess156d4Regs. cbn.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate. exact Hmstatus1. }
  destruct (segment_156d8_mstatus_covered r2 global observations2 middle2
    Hpc2 Hx1_2 Hcodebc HcodeInt Hmstatus2 Hseg2) as (Hmiddle2 & Hobs2).
  subst observations2.
  have Hsegments2 : segments2 = [] by (inversion Hrun2; reflexivity).
  have Hmachine : middle2 = after.1 by (inversion Hrun2; reflexivity).
  rewrite Hmiddle2 in Hmachine.
  destruct after as [afterMachine afterLog].
  cbn in Hmachine, Hlog |- *.
  subst afterMachine.
  f_equal.
  cbn [flattenMicroObservations] in Hlog.
  unfold writeSuccess156d0Observations,
    writeSuccess156d0PrefixObservations,
    writeSuccess156d0PreReadObservations,
    writeSuccess156d0PostReadPrefix,
    writeSuccess156d4Observations,
    writeSuccess156d4PrefixObservations,
    writeSuccess156d8Observations,
    writeSuccess156d8PrefixObservations in Hlog.
  rewrite Hsegments2 in Hlog.
  cbn [segmentRecords segmentRecordsFrom flattenMicroObservations] in Hlog.
  rewrite app_nil_r in Hlog.
  exact Hlog.
Qed.

Print Assumptions writeSuccessWithdrawals156d0EncoderIntCoveredDirect.
