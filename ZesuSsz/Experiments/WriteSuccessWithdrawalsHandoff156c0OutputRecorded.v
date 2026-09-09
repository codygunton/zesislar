From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_93.a156c0.
Require Import IslaTraces.write_success_93.a156c4.
Require Import IslaTraces.write_success_93.a156c8.
Require Import IslaTraces.write_success_93.a156cc.
Require Import IslaTraces.write_success_01.a10190.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156cc.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Lemma writeSuccessWithdrawals156c0OutputRecordedDirect regs global
    (data : bv 64) priorLog oldX11 oldX10 oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c0)) ->
  regs !! "x11" = Some oldX11 ->
  regs !! "x18" = Some (RVal_Bits data) ->
  regs !! "x10" = Some oldX10 ->
  regs !! "x1" = Some oldX1 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  writeSuccessWithdrawalsInstructionTable global ->
  exists segments,
    WriteSuccessWithdrawalsRecordedRun 4
      (writeSuccess156c0Before regs global, priorLog) segments
      (writeSuccess156ccAfter
        (writeSuccess156c8Regs
          (writeSuccess156c4Regs (writeSuccess156c0Regs regs) data)) global,
       priorLog).
Proof.
  intros Hpc Hx11 Hx18 Hx10 Hx1 Hmstatus Htable.
  have Hc0 := Htable 0x156c0 a156c0 ltac:(cbn; tauto).
  have Hc4 := Htable 0x156c4 a156c4 ltac:(cbn; tauto).
  have Hc8 := Htable 0x156c8 a156c8 ltac:(cbn; tauto).
  have Hcc := Htable 0x156cc a156cc ltac:(cbn; tauto).
  have Hout := Htable 0x10190 a10190 ltac:(cbn; tauto).
  set (r1 := writeSuccess156c0Regs regs).
  set (r2 := writeSuccess156c4Regs r1 data).
  set (r3 := writeSuccess156c8Regs r2).
  set (o0 := writeSuccess156c0Observations regs global).
  have Hall0 := segment_156c0_mstatus regs global oldX11 Hpc Hx11 Hc0 Hc4
    Hmstatus.
  have Hseg0 : IslaInstructionSegment (writeSuccess156c0Before regs global) o0
      (writeSuccess156c4Before r1 global).
  { unfold o0, r1, writeSuccess156c4Before. exact (proj1 Hall0). }
  have Hsilent0 : concat (map microLabels o0) = [] :=
    proj2 (proj2 (proj2 Hall0)).
  have Hpc1 : r1 !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c4)).
  { unfold r1, writeSuccess156c0Regs. rewrite lookup_insert.
    rewrite writeSuccess156c0NextPcExact. reflexivity. }
  have Hx18_1 : r1 !! "x18" = Some (RVal_Bits data).
  { unfold r1. rewrite writeSuccess156c0RegsLookupOther; try discriminate.
    exact Hx18. }
  have Hx10_1 : r1 !! "x10" = Some oldX10.
  { unfold r1. rewrite writeSuccess156c0RegsLookupOther; try discriminate.
    exact Hx10. }
  have Hmstatus1 : eval_a_exp r1 writeSuccess156c4Mstatus =
      Some (Val_Bool true).
  { unfold r1, writeSuccess156c0Regs. cbn.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate. exact Hmstatus. }
  set (o1 := writeSuccess156c4Observations r1 global data).
  have Hall1 := segment_156c4_mstatus r1 global data oldX10 Hpc1 Hx18_1
    Hx10_1 Hc4 Hc8 Hmstatus1.
  have Hseg1 : IslaInstructionSegment (writeSuccess156c4Before r1 global) o1
      (writeSuccess156c8Before r2 global).
  { unfold o1, r2, writeSuccess156c8Before. exact (proj1 Hall1). }
  have Hsilent1 : concat (map microLabels o1) = [] :=
    proj2 (proj2 (proj2 Hall1)).
  have Hpc2 : r2 !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c8)).
  { unfold r2, writeSuccess156c4Regs. rewrite lookup_insert.
    rewrite writeSuccess156c4NextPcExact. reflexivity. }
  have Hx1_2 : r2 !! "x1" = Some oldX1.
  { unfold r2. rewrite writeSuccess156c4RegsLookupOther; try discriminate.
    unfold r1. rewrite writeSuccess156c0RegsLookupOther; try discriminate.
    exact Hx1. }
  have Hmstatus2 : eval_a_exp r2 writeSuccess15694Mstatus =
      Some (Val_Bool true).
  { unfold r2, writeSuccess156c4Regs. cbn.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate. exact Hmstatus1. }
  set (o2 := writeSuccess156c8Observations r2 global).
  have Hall2 := segment_156c8_mstatus r2 global oldX1 Hpc2 Hx1_2 Hc8 Hcc
    Hmstatus2.
  have Hseg2 : IslaInstructionSegment (writeSuccess156c8Before r2 global) o2
      (writeSuccess156ccBefore r3 global).
  { unfold o2, r3, writeSuccess156ccBefore. exact (proj1 Hall2). }
  have Hsilent2 : concat (map microLabels o2) = [] :=
    proj2 (proj2 (proj2 Hall2)).
  have Hpc3 : r3 !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156cc)).
  { unfold r3, writeSuccess156c8Regs. rewrite lookup_insert.
    rewrite writeSuccess156c8NextPcExact. reflexivity. }
  have Hx1_3 : r3 !! "x1" = Some (RVal_Bits writeSuccess156ccRa).
  { unfold r3, writeSuccess156c8Regs. rewrite lookup_insert_ne;
      last discriminate. rewrite lookup_insert. reflexivity. }
  have Hmstatus3 : eval_a_exp r3 writeSuccess15694Mstatus =
      Some (Val_Bool true).
  { unfold r3, writeSuccess156c8Regs. cbn.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate. exact Hmstatus2. }
  set (o3 := writeSuccess156ccObservations r3 global).
  have Hall3 := segment_156cc_mstatus r3 global Hpc3 Hx1_3 Hcc Hout Hmstatus3.
  have Hseg3 : IslaInstructionSegment (writeSuccess156ccBefore r3 global) o3
      (writeSuccess156ccAfter r3 global).
  { unfold o3. exact (proj1 Hall3). }
  have Hsilent3 : concat (map microLabels o3) = [] :=
    proj2 (proj2 (proj2 Hall3)).
  have Hr0 := writeSuccessWithdrawalsRecordedRunZero
    (writeSuccess156c0Before regs global, priorLog).
  have Hr1 := writeSuccessWithdrawalsSilentRecordedSnoc 0 _ [] _ o0 _ Hr0
    Hseg0 Hsilent0.
  have Hr2 := writeSuccessWithdrawalsSilentRecordedSnoc 1 _ [o0] _ o1 _ Hr1
    Hseg1 Hsilent1.
  have Hr3 := writeSuccessWithdrawalsSilentRecordedSnoc 2 _ [o0; o1] _ o2 _ Hr2
    Hseg2 Hsilent2.
  have Hr4 := writeSuccessWithdrawalsSilentRecordedSnoc 3 _ [o0; o1; o2] _ o3
    _ Hr3 Hseg3 Hsilent3.
  exists [o0; o1; o2; o3]. exact Hr4.
Qed.

Print Assumptions writeSuccessWithdrawals156c0OutputRecordedDirect.
