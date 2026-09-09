From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_95.a156dc.
Require Import IslaTraces.write_success_95.a156e0.
Require Import IslaTraces.write_success_95.a156e4.
Require Import IslaTraces.write_success_96.a156e8.
Require Import IslaTraces.write_success_90.a15694.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156dc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e4.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessWithdrawalsCounterDecrementS remaining :
  (Z_to_bv 64 (Z.of_nat (S remaining)) + BV 64 18446744073709551615)%bv =
  Z_to_bv 64 (Z.of_nat remaining).
Proof.
  replace (BV 64 18446744073709551615) with (Z_to_bv 64 (-1)) by
    (apply bv_eq; vm_compute; reflexivity).
  rewrite writeSuccessZToBvAddOperational. f_equal. lia.
Qed.

Lemma writeSuccessWithdrawals156dcLoopTailRecordedDirect regs global
    (pointer : bv 64) remaining priorLog :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156dc)) ->
  regs !! "x8" = Some (RVal_Bits pointer) ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  eval_a_exp regs writeSuccess156dcMstatus = Some (Val_Bool true) ->
  writeSuccessWithdrawalsInstructionTable global ->
  exists segments,
    WriteSuccessWithdrawalsRecordedRun 3
      (writeSuccess156dcBefore regs global, priorLog) segments
      (writeSuccess156e4After (Z_to_bv 64 (Z.of_nat remaining))
        (writeSuccess156e0Regs (writeSuccess156dcRegs regs pointer)
          (Z_to_bv 64 (Z.of_nat (S remaining)))) global,
       priorLog).
Proof.
  intros Hpc Hx8 Hx9 Hmstatus Htable.
  have Hdc := Htable 0x156dc a156dc ltac:(cbn; tauto).
  have He0 := Htable 0x156e0 a156e0 ltac:(cbn; tauto).
  have He4 := Htable 0x156e4 a156e4 ltac:(cbn; tauto).
  have He8 := Htable 0x156e8 a156e8 ltac:(cbn; tauto).
  have H94 := Htable 0x15694 a15694 ltac:(cbn; tauto).
  set (r1 := writeSuccess156dcRegs regs pointer).
  set (r2 := writeSuccess156e0Regs r1
    (Z_to_bv 64 (Z.of_nat (S remaining)))).
  set (next := Z_to_bv 64 (Z.of_nat remaining)).
  set (o0 := writeSuccess156dcObservations regs global pointer).
  have Hall0 := segment_156dc_mstatus regs global pointer (RVal_Bits pointer)
    Hpc Hx8 Hx8 Hdc He0 Hmstatus.
  have Hseg0 : IslaInstructionSegment (writeSuccess156dcBefore regs global) o0
      (writeSuccess156e0Before r1 global).
  { unfold o0, r1, writeSuccess156e0Before. exact (proj1 Hall0). }
  have Hsilent0 : concat (map microLabels o0) = [] :=
    proj2 (proj2 (proj2 Hall0)).
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
  set (o1 := writeSuccess156e0Observations r1 global
    (Z_to_bv 64 (Z.of_nat (S remaining)))).
  have Hall1 := segment_156e0_mstatus r1 global
    (Z_to_bv 64 (Z.of_nat (S remaining)))
    (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) Hpc1 Hx9_1 Hx9_1
    He0 He4 Hm1.
  have Hseg1 : IslaInstructionSegment (writeSuccess156e0Before r1 global) o1
      (writeSuccess156e4Before r2 global).
  { unfold o1, r2, writeSuccess156e4Before. exact (proj1 Hall1). }
  have Hsilent1 : concat (map microLabels o1) = [] :=
    proj2 (proj2 (proj2 Hall1)).
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
  set (o2 := writeSuccess156e4Observations next r2 global).
  have Hseg2 : IslaInstructionSegment (writeSuccess156e4Before r2 global) o2
      (writeSuccess156e4After next r2 global).
  { unfold o2. apply segment_156e4_mstatus; assumption. }
  have Hsilent2 : concat (map microLabels o2) = [].
  { unfold o2, writeSuccess156e4Observations.
    destruct (decide (next = BV 64 0)); reflexivity. }
  have Hr0 := writeSuccessWithdrawalsRecordedRunZero
    (writeSuccess156dcBefore regs global, priorLog).
  have Hr1 := writeSuccessWithdrawalsSilentRecordedSnoc 0 _ [] _ o0 _ Hr0
    Hseg0 Hsilent0.
  have Hr2 := writeSuccessWithdrawalsSilentRecordedSnoc 1 _ [o0] _ o1 _ Hr1
    Hseg1 Hsilent1.
  have Hr3 := writeSuccessWithdrawalsSilentRecordedSnoc 2 _ [o0; o1] _ o2 _ Hr2
    Hseg2 Hsilent2.
  exists [o0; o1; o2]. exact Hr3.
Qed.

Print Assumptions writeSuccessWithdrawalsCounterDecrementS.
Print Assumptions writeSuccessWithdrawals156dcLoopTailRecordedDirect.
