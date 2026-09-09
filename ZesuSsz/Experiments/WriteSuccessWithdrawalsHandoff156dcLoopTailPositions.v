From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_95.a156dc.
Require Import IslaTraces.write_success_95.a156e0.
Require Import IslaTraces.write_success_95.a156e4.
Require Import IslaTraces.write_success_96.a156e8.
Require Import IslaTraces.write_success_90.a15694.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156dc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156dcCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e0Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e4Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156dcLoopTailRecorded.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessWithdrawalsSilentSegmentRecordsFrom memory observations :
  concat (map microLabels observations) = [] ->
  segmentRecordsFrom memory observations = [].
Proof.
  revert memory. induction observations as [|observation observations IH];
    intros memory Hlabels; first reflexivity.
  cbn in Hlabels. apply app_eq_nil in Hlabels as [Hhead Htail].
  cbn. rewrite Hhead. cbn. apply IH. exact Htail.
Qed.

Lemma writeSuccessWithdrawals156dcLoopTailPositionsExact regs global
    (pointer : bv 64) remaining priorLog segments after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156dc)) ->
  regs !! "x8" = Some (RVal_Bits pointer) ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  eval_a_exp regs writeSuccess156dcMstatus = Some (Val_Bool true) ->
  writeSuccessWithdrawalsInstructionTable global ->
  WriteSuccessWithdrawalsRecordedRun 3
    (writeSuccess156dcBefore regs global, priorLog) segments after ->
  after =
    (writeSuccess156e4After (Z_to_bv 64 (Z.of_nat remaining))
      (writeSuccess156e0Regs (writeSuccess156dcRegs regs pointer)
        (Z_to_bv 64 (Z.of_nat (S remaining)))) global,
     priorLog) /\
  segments =
    [writeSuccess156dcObservations regs global pointer;
     writeSuccess156e0Observations (writeSuccess156dcRegs regs pointer) global
       (Z_to_bv 64 (Z.of_nat (S remaining)));
     writeSuccess156e4Observations (Z_to_bv 64 (Z.of_nat remaining))
       (writeSuccess156e0Regs (writeSuccess156dcRegs regs pointer)
         (Z_to_bv 64 (Z.of_nat (S remaining)))) global].
Proof.
  intros Hpc Hx8 Hx9 Hmstatus Htable (Hrun & Hlog).
  have Hdc := Htable 0x156dc a156dc ltac:(cbn; tauto).
  have He0 := Htable 0x156e0 a156e0 ltac:(cbn; tauto).
  have He4 := Htable 0x156e4 a156e4 ltac:(cbn; tauto).
  have He8 := Htable 0x156e8 a156e8 ltac:(cbn; tauto).
  have H94 := Htable 0x15694 a15694 ltac:(cbn; tauto).
  inversion Hrun as [|? ? o0 s1 gs1 z1 Hs0 Hr1]; subst.
  inversion Hr1 as [|? ? o1 s2 gs2 z2 Hs1 Hr2]; subst.
  inversion Hr2 as [|? ? o2 s3 gs3 z3 Hs2 Hr3]; subst.
  destruct (segment_156dc_mstatus_covered regs global pointer
    (RVal_Bits pointer) o0 s1 Hpc Hx8 Hx8 Hdc He0 Hmstatus Hs0) as
    (Hs1eq & Ho0). subst s1 o0.
  set (r1 := writeSuccess156dcRegs regs pointer).
  have Hpc1 : r1 !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156e0)).
  { unfold r1, writeSuccess156dcRegs. rewrite lookup_insert.
    rewrite writeSuccess156dcNextPcExact. reflexivity. }
  have Hx9_1 : r1 !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold r1. rewrite writeSuccess156dcRegsLookupOther; try discriminate.
    exact Hx9. }
  have Hm1 : eval_a_exp r1 writeSuccess156e0Mstatus = Some (Val_Bool true).
  { unfold r1, writeSuccess156dcRegs. cbn.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate. exact Hmstatus. }
  destruct (segment_156e0_mstatus_covered r1 global
    (Z_to_bv 64 (Z.of_nat (S remaining)))
    (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) o1 s2 Hpc1 Hx9_1 Hx9_1
    He0 He4 Hm1 Hs1) as (Hs2eq & Ho1). subst s2 o1.
  set (r2 := writeSuccess156e0Regs r1
    (Z_to_bv 64 (Z.of_nat (S remaining)))).
  set (next := Z_to_bv 64 (Z.of_nat remaining)).
  have Hpc2 : r2 !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156e4)).
  { unfold r2, writeSuccess156e0Regs. rewrite lookup_insert.
    rewrite writeSuccess156e0NextPcExact. reflexivity. }
  have Hx9_2 : r2 !! "x9" = Some (RVal_Bits next).
  { unfold r2, next, writeSuccess156e0Regs. rewrite lookup_insert_ne;
      last discriminate. rewrite lookup_insert.
    rewrite writeSuccessWithdrawalsCounterDecrementS. reflexivity. }
  have Hm2 : eval_a_exp r2 writeSuccess15694Mstatus = Some (Val_Bool true).
  { unfold r2, writeSuccess156e0Regs. cbn.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate. exact Hm1. }
  destruct (segment_156e4_mstatus_covered r2 global next o2 s3 Hpc2 Hx9_2
    He4 He8 H94 Hm2 Hs2) as (Hs3eq & Ho2). subst o2.
  have Htail : gs3 = [] by (inversion Hr3; reflexivity).
  have Hmachine : s3 = after.1 by (inversion Hr3; reflexivity).
  rewrite Hs3eq in Hmachine.
  split.
  - destruct after as [afterMachine afterLog]. cbn in Hmachine, Hlog |- *.
  subst afterMachine. f_equal.
  rewrite Htail in Hlog.
  unfold writeSuccess156dcObservations, writeSuccess156dcPrefixObservations,
    writeSuccess156e0Observations, writeSuccess156e0PrefixObservations,
    writeSuccess156e4Observations,
    writeSuccess156e4FallthroughAllObservations,
    writeSuccess156e4TakenAllObservations,
    writeSuccess156e4CommonObservations,
    writeSuccess156e4CommonLocals,
    writeSuccess156e4FallthroughObservations,
    writeSuccess156e4FallthroughLocals,
    writeSuccess156e4TakenObservations,
    writeSuccess156e4TakenLocals in Hlog.
  destruct (decide (next = BV 64 0)).
  + cbn [writeSuccess15694Observation flattenMicroObservations] in Hlog.
    rewrite writeSuccessWithdrawalsSilentSegmentRecordsFrom in Hlog;
      last reflexivity.
    rewrite app_nil_r in Hlog. exact Hlog.
  + cbn [writeSuccess15694Observation flattenMicroObservations] in Hlog.
    rewrite writeSuccessWithdrawalsSilentSegmentRecordsFrom in Hlog;
      last reflexivity.
    rewrite app_nil_r in Hlog. exact Hlog.
  - rewrite Htail. reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawals156dcLoopTailPositionsExact.

(* The exact segment list binds the three tail positions to the supplied run. *)
