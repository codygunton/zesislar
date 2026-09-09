From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_94.a156d0.
Require Import IslaTraces.write_success_94.a156d4.
Require Import IslaTraces.write_success_94.a156d8.
Require Import IslaTraces.write_success_07.a15d10.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Lemma writeSuccessWithdrawals156d0EncoderIntRecordedDirect regs global
    (sp value : bv 64)
    priorLog (mstatusBits satp oldDest : bv 64) (oldX1 : valu) :
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
  exists segments,
    WriteSuccessWithdrawalsRecordedRun 3
      (writeSuccess156d0Before regs global, priorLog) segments
      (writeSuccess156d8After
        (writeSuccess156d4Regs (writeSuccess156d0Regs regs value)) global,
       priorLog).
Proof.
  intros Hpc Hsp Hmstatus Hsatp Hdest Hx1 Hsys HmstatusAssume Haligned
    Hlower Hupper Hread Htable.
  have Hcodeb4 : global.(seq_instrs) !! Z_to_bv 64 0x156d0 = Some a156d0.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hcodeb8 : global.(seq_instrs) !! Z_to_bv 64 0x156d4 = Some a156d4.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hcodebc : global.(seq_instrs) !! Z_to_bv 64 0x156d8 = Some a156d8.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have HcodeInt : global.(seq_instrs) !! Z_to_bv 64 0x15d10 = Some a15d10.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  set (r1 := writeSuccess156d0Regs regs value).
  set (r2 := writeSuccess156d4Regs r1).
  set (o0 := writeSuccess156d0Observations regs global mstatusBits sp satp value).
  have Hall0 := segment_156d0 regs global mstatusBits sp satp value oldDest
    Hpc Hsp Hmstatus Hsatp Hdest Hsys HmstatusAssume Haligned Hlower Hupper
    Hread Hcodeb4 Hcodeb8.
  have Hseg0 : IslaInstructionSegment (writeSuccess156d0Before regs global) o0
      (writeSuccess156d4Before r1 global).
  { unfold o0, r1, writeSuccess156d4Before. exact (proj1 Hall0). }
  have Hsilent0 : concat (map microLabels o0) = [].
  { unfold o0, writeSuccess156d0Observations,
      writeSuccess156d0PrefixObservations,
      writeSuccess156d0PreReadObservations,
      writeSuccess156d0PostReadPrefix. reflexivity. }
  have Hpc1 : r1 !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156d4)).
  { unfold r1, writeSuccess156d0Regs. rewrite lookup_insert.
    rewrite writeSuccess156d0NextPcExact. reflexivity. }
  have Hx1_1 : r1 !! "x1" = Some oldX1.
  { unfold r1. rewrite writeSuccess156d0RegsLookupOther; try discriminate.
    exact Hx1. }
  have Hmstatus1 : eval_a_exp r1 writeSuccess15694Mstatus =
      Some (Val_Bool true).
  { unfold r1, writeSuccess156d0Regs in *.
    cbn. rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate. exact HmstatusAssume. }
  set (o1 := writeSuccess156d4Observations r1 global).
  have Hall1 := segment_156d4_mstatus r1 global oldX1 Hpc1 Hx1_1 Hcodeb8
    Hcodebc Hmstatus1.
  have Hseg1 : IslaInstructionSegment (writeSuccess156d4Before r1 global) o1
      (writeSuccess156d8Before r2 global).
  { unfold o1, r2, writeSuccess156d8Before. exact (proj1 Hall1). }
  have Hsilent1 : concat (map microLabels o1) = [] :=
    proj2 (proj2 (proj2 Hall1)).
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
  set (o2 := writeSuccess156d8Observations r2 global).
  have Hall2 := segment_156d8_mstatus r2 global Hpc2 Hx1_2 Hcodebc HcodeInt
    Hmstatus2.
  have Hseg2 : IslaInstructionSegment (writeSuccess156d8Before r2 global) o2
      (writeSuccess156d8After r2 global).
  { unfold o2. exact (proj1 Hall2). }
  have Hsilent2 : concat (map microLabels o2) = [] :=
    proj2 (proj2 (proj2 Hall2)).
  have Hr0 := writeSuccessWithdrawalsRecordedRunZero
    (writeSuccess156d0Before regs global, priorLog).
  have Hr1 := writeSuccessWithdrawalsSilentRecordedSnoc 0 _ [] _ o0 _ Hr0
    Hseg0 Hsilent0.
  have Hr2 := writeSuccessWithdrawalsSilentRecordedSnoc 1 _ [o0] _ o1 _ Hr1
    Hseg1 Hsilent1.
  have Hr3 := writeSuccessWithdrawalsSilentRecordedSnoc 2 _ [o0; o1] _ o2 _ Hr2
    Hseg2 Hsilent2.
  exists [o0; o1; o2]. exact Hr3.
Qed.

Print Assumptions writeSuccessWithdrawals156d0EncoderIntRecordedDirect.
