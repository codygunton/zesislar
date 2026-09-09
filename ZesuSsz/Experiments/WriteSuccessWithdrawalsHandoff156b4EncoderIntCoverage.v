From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_92.a156b4.
Require Import IslaTraces.write_success_92.a156b8.
Require Import IslaTraces.write_success_92.a156bc.
Require Import IslaTraces.write_success_07.a15d10.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b4Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b8Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156bc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156bcCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4EncoderIntRecorded.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Lemma writeSuccessWithdrawals156b4EncoderIntCoveredDirect regs global
    (sp value : bv 64) priorLog (mstatusBits satp oldDest : bv 64)
    (oldX1 : valu) segments after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "mstatus" =
    Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x10" = Some (RVal_Bits oldDest) ->
  regs !! "x1" = Some oldX1 ->
  writeSuccess156b4SysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156b4Aligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156b4Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156b4Upper = Some (Val_Bool true) ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess156b4Address sp)) 8 =
    Some (bv_to_bvn value) ->
  writeSuccessWithdrawalsInstructionTable global ->
  WriteSuccessWithdrawalsRecordedRun 3
    (writeSuccess156b4Before regs global, priorLog) segments after ->
  after =
    (writeSuccess156bcAfter
      (writeSuccess156b8Regs (writeSuccess156b4Regs regs value)) global,
     priorLog).
Proof.
  intros Hpc Hsp Hmstatus Hsatp Hdest Hx1 Hsys HmstatusAssume Haligned
    Hlower Hupper Hread Htable Hrecorded.
  have Hcodeb4 := Htable 0x156b4 a156b4 ltac:(cbn; tauto).
  have Hcodeb8 := Htable 0x156b8 a156b8 ltac:(cbn; tauto).
  have Hcodebc := Htable 0x156bc a156bc ltac:(cbn; tauto).
  have HcodeInt := Htable 0x15d10 a15d10 ltac:(cbn; tauto).
  destruct Hrecorded as (Hrun & Hlog).
  inversion Hrun as
    [|? ? observations0 middle0 segments0 machineAfter0 Hseg0 Hrun0]; subst.
  inversion Hrun0 as
    [|? ? observations1 middle1 segments1 machineAfter1 Hseg1 Hrun1]; subst.
  inversion Hrun1 as
    [|? ? observations2 middle2 segments2 machineAfter2 Hseg2 Hrun2]; subst.
  destruct (segment_156b4_covered regs global mstatusBits sp satp value oldDest
    observations0 middle0 Hpc Hsp Hmstatus Hsatp Hdest Hsys HmstatusAssume
    Haligned Hlower Hupper Hread Hcodeb4 Hcodeb8 Hseg0) as (Hmiddle0 & Hobs0).
  subst middle0 observations0.
  have Hpc1 : writeSuccess156b4Regs regs value !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x156b8)).
  { unfold writeSuccess156b4Regs. rewrite lookup_insert.
    rewrite writeSuccess156b4NextPcExact. reflexivity. }
  have Hx1_1 : writeSuccess156b4Regs regs value !! "x1" = Some oldX1.
  { rewrite writeSuccess156b4RegsLookupOther; try discriminate. exact Hx1. }
  have Hmstatus1 : eval_a_exp (writeSuccess156b4Regs regs value)
      writeSuccess15694Mstatus = Some (Val_Bool true).
  { unfold writeSuccess156b4Regs. cbn.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate. exact HmstatusAssume. }
  destruct (segment_156b8_mstatus_covered (writeSuccess156b4Regs regs value)
    global oldX1 observations1 middle1 Hpc1 Hx1_1 Hcodeb8 Hcodebc Hmstatus1
    Hseg1) as (Hmiddle1 & Hobs1).
  subst middle1 observations1.
  set (r2 := writeSuccess156b8Regs (writeSuccess156b4Regs regs value)).
  have Hpc2 : r2 !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156bc)).
  { unfold r2, writeSuccess156b8Regs. rewrite lookup_insert.
    rewrite writeSuccess156b8NextPcExact. reflexivity. }
  have Hx1_2 : r2 !! "x1" = Some (RVal_Bits writeSuccess156bcRa).
  { unfold r2, writeSuccess156b8Regs. rewrite lookup_insert_ne;
      last discriminate. rewrite lookup_insert. reflexivity. }
  have Hmstatus2 : eval_a_exp r2 writeSuccess15694Mstatus =
      Some (Val_Bool true).
  { unfold r2, writeSuccess156b8Regs. cbn.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate. exact Hmstatus1. }
  destruct (segment_156bc_mstatus_covered r2 global observations2 middle2
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
  unfold writeSuccess156b4Observations,
    writeSuccess156b4PrefixObservations,
    writeSuccess156b4PreReadObservations,
    writeSuccess156b4PostReadPrefix,
    writeSuccess156b8Observations,
    writeSuccess156b8PrefixObservations,
    writeSuccess156bcObservations,
    writeSuccess156bcPrefixObservations in Hlog.
  rewrite Hsegments2 in Hlog.
  cbn [segmentRecords segmentRecordsFrom flattenMicroObservations] in Hlog.
  rewrite app_nil_r in Hlog.
  exact Hlog.
Qed.

Print Assumptions writeSuccessWithdrawals156b4EncoderIntCoveredDirect.
