From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_93.a156c0.
Require Import IslaTraces.write_success_93.a156c4.
Require Import IslaTraces.write_success_93.a156c8.
Require Import IslaTraces.write_success_93.a156cc.
Require Import IslaTraces.write_success_01.a10190.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c4Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c8Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156cc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156ccCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputRecorded.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Lemma writeSuccessWithdrawals156c0OutputCoveredDirect regs global
    (data : bv 64) priorLog oldX11 oldX10 oldX1 segments after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c0)) ->
  regs !! "x11" = Some oldX11 ->
  regs !! "x18" = Some (RVal_Bits data) ->
  regs !! "x10" = Some oldX10 ->
  regs !! "x1" = Some oldX1 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  writeSuccessWithdrawalsInstructionTable global ->
  WriteSuccessWithdrawalsRecordedRun 4
    (writeSuccess156c0Before regs global, priorLog) segments after ->
  after =
    (writeSuccess156ccAfter
      (writeSuccess156c8Regs
        (writeSuccess156c4Regs (writeSuccess156c0Regs regs) data)) global,
     priorLog).
Proof.
  intros Hpc Hx11 Hx18 Hx10 Hx1 Hmstatus Htable (Hrun & Hlog).
  have Hc0 := Htable 0x156c0 a156c0 ltac:(cbn; tauto).
  have Hc4 := Htable 0x156c4 a156c4 ltac:(cbn; tauto).
  have Hc8 := Htable 0x156c8 a156c8 ltac:(cbn; tauto).
  have Hcc := Htable 0x156cc a156cc ltac:(cbn; tauto).
  have Hout := Htable 0x10190 a10190 ltac:(cbn; tauto).
  inversion Hrun as [|? ? o0 s1 gs1 z1 Hs0 Hr1]; subst.
  inversion Hr1 as [|? ? o1 s2 gs2 z2 Hs1 Hr2]; subst.
  inversion Hr2 as [|? ? o2 s3 gs3 z3 Hs2 Hr3]; subst.
  inversion Hr3 as [|? ? o3 s4 gs4 z4 Hs3 Hr4]; subst.
  set (r1 := writeSuccess156c0Regs regs).
  destruct (segment_156c0_mstatus_covered regs global oldX11 o0 s1 Hpc Hx11
    Hc0 Hc4 Hmstatus Hs0) as (Hs1eq & Ho0). subst s1 o0.
  have Hpc1 : r1 !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c4)).
  { unfold r1, writeSuccess156c0Regs. rewrite lookup_insert.
    rewrite writeSuccess156c0NextPcExact. reflexivity. }
  have Hx18_1 : r1 !! "x18" = Some (RVal_Bits data).
  { unfold r1. rewrite writeSuccess156c0RegsLookupOther; try discriminate.
    exact Hx18. }
  have Hx10_1 : r1 !! "x10" = Some oldX10.
  { unfold r1. rewrite writeSuccess156c0RegsLookupOther; try discriminate.
    exact Hx10. }
  have Hm1 : eval_a_exp r1 writeSuccess156c4Mstatus = Some (Val_Bool true).
  { unfold r1, writeSuccess156c0Regs. cbn.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate. exact Hmstatus. }
  destruct (segment_156c4_mstatus_covered r1 global data oldX10 o1 s2 Hpc1
    Hx18_1 Hx10_1 Hc4 Hc8 Hm1 Hs1) as (Hs2eq & Ho1). subst s2 o1.
  set (r2 := writeSuccess156c4Regs r1 data).
  have Hpc2 : r2 !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c8)).
  { unfold r2, writeSuccess156c4Regs. rewrite lookup_insert.
    rewrite writeSuccess156c4NextPcExact. reflexivity. }
  have Hx1_2 : r2 !! "x1" = Some oldX1.
  { unfold r2. rewrite writeSuccess156c4RegsLookupOther; try discriminate.
    unfold r1. rewrite writeSuccess156c0RegsLookupOther; try discriminate.
    exact Hx1. }
  have Hm2 : eval_a_exp r2 writeSuccess15694Mstatus = Some (Val_Bool true).
  { unfold r2, writeSuccess156c4Regs. cbn.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate. exact Hm1. }
  destruct (segment_156c8_mstatus_covered r2 global oldX1 o2 s3 Hpc2 Hx1_2
    Hc8 Hcc Hm2 Hs2) as (Hs3eq & Ho2). subst s3 o2.
  set (r3 := writeSuccess156c8Regs r2).
  have Hpc3 : r3 !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156cc)).
  { unfold r3, writeSuccess156c8Regs. rewrite lookup_insert.
    rewrite writeSuccess156c8NextPcExact. reflexivity. }
  have Hx1_3 : r3 !! "x1" = Some (RVal_Bits writeSuccess156ccRa).
  { unfold r3, writeSuccess156c8Regs. rewrite lookup_insert_ne;
      last discriminate. rewrite lookup_insert. reflexivity. }
  have Hm3 : eval_a_exp r3 writeSuccess15694Mstatus = Some (Val_Bool true).
  { unfold r3, writeSuccess156c8Regs. cbn.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate. exact Hm2. }
  destruct (segment_156cc_mstatus_covered r3 global o3 s4 Hpc3 Hx1_3 Hcc
    Hout Hm3 Hs3) as (Hs4eq & Ho3). subst o3.
  have Htail : gs4 = [] by (inversion Hr4; reflexivity).
  have Hmachine : s4 = after.1 by (inversion Hr4; reflexivity).
  rewrite Hs4eq in Hmachine.
  destruct after as [afterMachine afterLog]. cbn in Hmachine, Hlog |- *.
  subst afterMachine. f_equal.
  rewrite Htail in Hlog.
  unfold writeSuccess156c0Observations, writeSuccess156c0PrefixObservations,
    writeSuccess156c4Observations, writeSuccess156c4PrefixObservations,
    writeSuccess156c8Observations, writeSuccess156c8PrefixObservations,
    writeSuccess156ccObservations, writeSuccess156ccPrefixObservations in Hlog.
  cbn [flattenMicroObservations segmentRecords segmentRecordsFrom] in Hlog.
  rewrite app_nil_r in Hlog. exact Hlog.
Qed.

Print Assumptions writeSuccessWithdrawals156c0OutputCoveredDirect.
