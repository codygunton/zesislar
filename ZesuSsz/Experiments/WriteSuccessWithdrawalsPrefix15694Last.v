From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_90.a156a0.
Require Import IslaTraces.write_success_90.a156a4.
Require Import IslaTraces.write_success_02.a101d4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a4.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessWithdrawalsPrefixLastAfter (before : IslaState) : IslaState :=
  writeSuccess156a4After
    (writeSuccess156a0After before.1.(seq_regs) before.2).1.(seq_regs)
    (writeSuccess156a0After before.1.(seq_regs) before.2).2.

Lemma writeSuccessWithdrawalsPrefix15694LastRecorded before priorLog oldX1 :
  before = writeSuccess156a0Before before.1.(seq_regs) before.2 ->
  before.1.(seq_regs) !! "PC" =
    Some (RVal_Bits (Z_to_bv 64 0x156a0)) ->
  before.1.(seq_regs) !! "x1" = Some oldX1 ->
  writeSuccessWithdrawalsInstructionTable before.2 ->
  eval_a_exp before.1.(seq_regs) writeSuccess15694Mstatus =
    Some (Val_Bool true) ->
  exists segments,
    WriteSuccessWithdrawalsRecordedRun 2 (before, priorLog) segments
      (writeSuccessWithdrawalsPrefixLastAfter before, priorLog).
Proof.
  intros Hbefore Hpca0 Hx1 Htable Hmstatus.
  have Hcodea0 : before.2.(seq_instrs) !! Z_to_bv 64 0x156a0 = Some a156a0.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hcodea4 : before.2.(seq_instrs) !! Z_to_bv 64 0x156a4 = Some a156a4.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hcode101d4 : before.2.(seq_instrs) !! Z_to_bv 64 0x101d4 = Some a101d4.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  set (sa4 := writeSuccess156a0After before.1.(seq_regs) before.2).
  set (send := writeSuccessWithdrawalsPrefixLastAfter before).
  set (oa0 := writeSuccess156a0Observations before.1.(seq_regs) before.2).
  have Ha0all := segment_156a0_mstatus _ _ oldX1 Hpca0 Hx1 Hcodea0 Hcodea4
    Hmstatus.
  have Hsega0 : IslaInstructionSegment before oa0 sa4.
  { unfold oa0, sa4. rewrite Hbefore. exact (proj1 Ha0all). }
  have Hsilenta0 := proj2 (proj2 (proj2 Ha0all)).
  have Hpca4 : sa4.1.(seq_regs) !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x156a4)).
  { unfold sa4, writeSuccess156a0After, writeSuccess15694Local,
      writeSuccess156a0Regs. cbn.
    rewrite lookup_insert writeSuccess156a0NextPcExact. reflexivity. }
  have Hx1_a4 : sa4.1.(seq_regs) !! "x1" =
      Some (RVal_Bits writeSuccess156a4Ra).
  { unfold sa4, writeSuccess156a0After, writeSuccess15694Local,
      writeSuccess156a0Regs, writeSuccess156a4Ra. cbn.
    rewrite lookup_insert_ne; try discriminate. rewrite lookup_insert.
    reflexivity. }
  have Hmstatusa4 : eval_a_exp sa4.1.(seq_regs) writeSuccess15694Mstatus =
      Some (Val_Bool true).
  { unfold sa4, writeSuccess156a0After, writeSuccess15694Local,
      writeSuccess156a0Regs, writeSuccess15694Mstatus in *. cbn in *.
    rewrite !lookup_insert_ne; try discriminate. exact Hmstatus. }
  set (oa4 := writeSuccess156a4Observations sa4.1.(seq_regs) sa4.2).
  have Ha4all := segment_156a4_mstatus _ _ Hpca4 Hx1_a4 Hcodea4 Hcode101d4
    Hmstatusa4.
  have Hsega4 : IslaInstructionSegment sa4 oa4 send.
  { unfold oa4, send, writeSuccessWithdrawalsPrefixLastAfter.
    exact (proj1 Ha4all). }
  have Hsilenta4 := proj2 (proj2 (proj2 Ha4all)).
  have Hr0 := writeSuccessWithdrawalsRecordedRunZero (before, priorLog).
  have Hra0 := writeSuccessWithdrawalsSilentRecordedSnoc 0
    (before, priorLog) [] (before, priorLog) oa0 sa4 Hr0 Hsega0 Hsilenta0.
  have Hra4 := writeSuccessWithdrawalsSilentRecordedSnoc 1
    (before, priorLog) [oa0] (sa4, priorLog) oa4 send Hra0 Hsega4 Hsilenta4.
  exists [oa0; oa4]. exact Hra4.
Qed.

Print Assumptions writeSuccessWithdrawalsPrefix15694LastRecorded.
