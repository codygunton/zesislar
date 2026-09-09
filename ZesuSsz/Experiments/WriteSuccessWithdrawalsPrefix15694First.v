From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import IslaTraces.write_success_90.a15694.
Require Import IslaTraces.write_success_90.a15698.
Require Import IslaTraces.write_success_90.a1569c.
Require Import IslaTraces.write_success_90.a156a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15698.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1569c.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessWithdrawalsPrefix15694FirstRecorded args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  exists segments oldX1,
    WriteSuccessWithdrawalsRecordedRun 3 state segments
      (writeSuccessWithdrawalsPrefixStatea0 state.1 sp pointer, priorLog) /\
    (writeSuccessWithdrawalsPrefixStatea0 state.1 sp pointer).1.(seq_regs) !!
      "x1" = Some oldX1 /\
    writeSuccessWithdrawalsInstructionTable
      (writeSuccessWithdrawalsPrefixStatea0 state.1 sp pointer).2 /\
    eval_a_exp
      (writeSuccessWithdrawalsPrefixStatea0 state.1 sp pointer).1.(seq_regs)
      writeSuccess15694Mstatus = Some (Val_Bool true).
Proof.
  intros Hinv.
  destruct (writeSuccessWithdrawalsInv15694DirectEntry args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state Hinv) as
    (oldX1 & oldX10 & oldX11 & oldX12 & Hentry & Hpc & Hx1 & Hsp & Hpointer &
     Hx10 & Hx11 & Hx12 & Htable & Hmstatus).
  have Hlog : state.2 = priorLog by (unfold Inv_15694 in Hinv; tauto).
  have Hcode94 : state.1.2.(seq_instrs) !! Z_to_bv 64 0x15694 = Some a15694.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hcode98 : state.1.2.(seq_instrs) !! Z_to_bv 64 0x15698 = Some a15698.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hcode9c : state.1.2.(seq_instrs) !! Z_to_bv 64 0x1569c = Some a1569c.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hcodea0 : state.1.2.(seq_instrs) !! Z_to_bv 64 0x156a0 = Some a156a0.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  set (s98 := writeSuccessWithdrawalsPrefixState98 state.1 sp).
  set (s9c := writeSuccessWithdrawalsPrefixState9c state.1 sp).
  set (sa0 := writeSuccessWithdrawalsPrefixStatea0 state.1 sp pointer).
  set (o94 := writeSuccess15694Observations state.1.1.(seq_regs) state.1.2 sp).
  have H94all := segment_15694_mstatus _ _ _ oldX10 Hpc Hsp Hx10 Hcode94
    Hcode98 Hmstatus.
  have Hseg94 : IslaInstructionSegment state.1 o94 s98.
  { unfold o94, s98, writeSuccessWithdrawalsPrefixState98.
    rewrite Hentry. exact (proj1 H94all). }
  have Hsilent94 := proj2 (proj2 (proj2 H94all)).
  have Hpc98 : s98.1.(seq_regs) !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x15698)).
  { unfold s98, writeSuccessWithdrawalsPrefixState98, writeSuccess15694After,
      writeSuccess15694Local, writeSuccess15694Regs. cbn.
    rewrite lookup_insert writeSuccess15694NextPcExact. reflexivity. }
  have Hx12_98 : s98.1.(seq_regs) !! "x12" = Some oldX12.
  { unfold s98, writeSuccessWithdrawalsPrefixState98, writeSuccess15694After,
      writeSuccess15694Local. cbn. rewrite writeSuccess15694RegsLookupOther;
      try discriminate. exact Hx12. }
  have Hmstatus98 : eval_a_exp s98.1.(seq_regs) writeSuccess15694Mstatus =
      Some (Val_Bool true).
  { unfold s98, writeSuccessWithdrawalsPrefixState98, writeSuccess15694After,
      writeSuccess15694Local, writeSuccess15694Regs,
      writeSuccess15694Mstatus in *. cbn in *.
    rewrite !lookup_insert_ne; try discriminate. exact Hmstatus. }
  set (o98 := writeSuccess15698Observations s98.1.(seq_regs) s98.2).
  have H98all := segment_15698_mstatus _ _ oldX12 Hpc98 Hx12_98 Hcode98
    Hcode9c Hmstatus98.
  have Hseg98 : IslaInstructionSegment s98 o98 s9c.
  { unfold o98, s9c, writeSuccessWithdrawalsPrefixState9c.
    exact (proj1 H98all). }
  have Hsilent98 := proj2 (proj2 (proj2 H98all)).
  have Hpc9c : s9c.1.(seq_regs) !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x1569c)).
  { unfold s9c, writeSuccessWithdrawalsPrefixState9c, writeSuccess15698After,
      writeSuccess15694Local, writeSuccess15698Regs. cbn.
    rewrite lookup_insert writeSuccess15698NextPcExact. reflexivity. }
  have Hx8_9c : s9c.1.(seq_regs) !! "x8" = Some (RVal_Bits pointer).
  { unfold s9c, s98, writeSuccessWithdrawalsPrefixState9c,
      writeSuccessWithdrawalsPrefixState98, writeSuccess15698After,
      writeSuccess15694After, writeSuccess15694Local. cbn.
    rewrite writeSuccess15698RegsLookupOther; try discriminate.
    rewrite writeSuccess15694RegsLookupOther; try discriminate. exact Hpointer. }
  have Hx11_9c : s9c.1.(seq_regs) !! "x11" = Some oldX11.
  { unfold s9c, s98, writeSuccessWithdrawalsPrefixState9c,
      writeSuccessWithdrawalsPrefixState98, writeSuccess15698After,
      writeSuccess15694After, writeSuccess15694Local. cbn.
    rewrite writeSuccess15698RegsLookupOther; try discriminate.
    rewrite writeSuccess15694RegsLookupOther; try discriminate. exact Hx11. }
  have Hmstatus9c : eval_a_exp s9c.1.(seq_regs) writeSuccess15694Mstatus =
      Some (Val_Bool true).
  { unfold s9c, s98, writeSuccessWithdrawalsPrefixState9c,
      writeSuccessWithdrawalsPrefixState98, writeSuccess15698After,
      writeSuccess15694After, writeSuccess15694Local, writeSuccess15698Regs,
      writeSuccess15694Regs,
      writeSuccess15694Mstatus in *. cbn in *.
    rewrite !lookup_insert_ne; try discriminate. exact Hmstatus. }
  set (o9c := writeSuccess1569cObservations s9c.1.(seq_regs) s9c.2 pointer).
  have H9call := segment_1569c_mstatus _ _ _ oldX11 Hpc9c Hx8_9c Hx11_9c
    Hcode9c Hcodea0 Hmstatus9c.
  have Hseg9c : IslaInstructionSegment s9c o9c sa0.
  { unfold o9c, sa0, writeSuccessWithdrawalsPrefixStatea0.
    exact (proj1 H9call). }
  have Hsilent9c := proj2 (proj2 (proj2 H9call)).
  have Hmstatusa0 : eval_a_exp sa0.1.(seq_regs) writeSuccess15694Mstatus =
      Some (Val_Bool true).
  { unfold sa0, s9c, s98, writeSuccessWithdrawalsPrefixStatea0,
      writeSuccessWithdrawalsPrefixState9c,
      writeSuccessWithdrawalsPrefixState98, writeSuccess1569cAfter,
      writeSuccess15698After, writeSuccess15694After, writeSuccess1569cLocal,
      writeSuccess15694Local, writeSuccess1569cRegs, writeSuccess15698Regs,
      writeSuccess15694Regs, writeSuccess15694Mstatus in *. cbn in *.
    rewrite !lookup_insert_ne; try discriminate. exact Hmstatus. }
  rewrite <- Hlog.
  have Hr0 := writeSuccessWithdrawalsRecordedRunZero state.
  have Hr94 := writeSuccessWithdrawalsSilentRecordedSnoc 0 state [] state o94
    s98 Hr0 Hseg94 Hsilent94.
  have Hr98 := writeSuccessWithdrawalsSilentRecordedSnoc 1 state [o94]
    (s98, state.2) o98 s9c Hr94 Hseg98 Hsilent98.
  have Hr9c := writeSuccessWithdrawalsSilentRecordedSnoc 2 state [o94; o98]
    (s9c, state.2) o9c sa0 Hr98 Hseg9c Hsilent9c.
  exists [o94; o98; o9c], oldX1. split; first exact Hr9c.
  repeat split.
  - unfold sa0, s9c, s98, writeSuccessWithdrawalsPrefixStatea0,
      writeSuccessWithdrawalsPrefixState9c,
      writeSuccessWithdrawalsPrefixState98, writeSuccess1569cAfter,
      writeSuccess15698After, writeSuccess15694After, writeSuccess1569cLocal,
      writeSuccess15694Local. cbn.
    rewrite writeSuccess1569cRegsLookupOther; try discriminate.
    rewrite writeSuccess15698RegsLookupOther; try discriminate.
    rewrite writeSuccess15694RegsLookupOther; try discriminate. exact Hx1.
  - unfold sa0, s9c, s98, writeSuccessWithdrawalsPrefixStatea0,
      writeSuccessWithdrawalsPrefixState9c,
      writeSuccessWithdrawalsPrefixState98, writeSuccess1569cAfter,
      writeSuccess15698After, writeSuccess15694After. cbn. exact Htable.
  - exact Hmstatusa0.
Qed.

Print Assumptions writeSuccessWithdrawalsPrefix15694FirstRecorded.
