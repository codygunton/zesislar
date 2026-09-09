From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_92.a156b4.
Require Import IslaTraces.write_success_92.a156b8.
Require Import IslaTraces.write_success_92.a156bc.
Require Import IslaTraces.write_success_07.a15d10.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156bc.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Lemma writeSuccessWithdrawals156b4EncoderIntRecordedDirect regs global
    (sp value : bv 64)
    priorLog (mstatusBits satp oldDest : bv 64) (oldX1 : valu) :
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
  exists segments,
    WriteSuccessWithdrawalsRecordedRun 3
      (writeSuccess156b4Before regs global, priorLog) segments
      (writeSuccess156bcAfter
        (writeSuccess156b8Regs (writeSuccess156b4Regs regs value)) global,
       priorLog).
Proof.
  intros Hpc Hsp Hmstatus Hsatp Hdest Hx1 Hsys HmstatusAssume Haligned
    Hlower Hupper Hread Htable.
  have Hcodeb4 : global.(seq_instrs) !! Z_to_bv 64 0x156b4 = Some a156b4.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hcodeb8 : global.(seq_instrs) !! Z_to_bv 64 0x156b8 = Some a156b8.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hcodebc : global.(seq_instrs) !! Z_to_bv 64 0x156bc = Some a156bc.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have HcodeInt : global.(seq_instrs) !! Z_to_bv 64 0x15d10 = Some a15d10.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  set (r1 := writeSuccess156b4Regs regs value).
  set (r2 := writeSuccess156b8Regs r1).
  set (o0 := writeSuccess156b4Observations regs global mstatusBits sp satp value).
  have Hall0 := segment_156b4 regs global mstatusBits sp satp value oldDest
    Hpc Hsp Hmstatus Hsatp Hdest Hsys HmstatusAssume Haligned Hlower Hupper
    Hread Hcodeb4 Hcodeb8.
  have Hseg0 : IslaInstructionSegment (writeSuccess156b4Before regs global) o0
      (writeSuccess156b8Before r1 global).
  { unfold o0, r1, writeSuccess156b8Before. exact (proj1 Hall0). }
  have Hsilent0 : concat (map microLabels o0) = [].
  { unfold o0, writeSuccess156b4Observations,
      writeSuccess156b4PrefixObservations,
      writeSuccess156b4PreReadObservations,
      writeSuccess156b4PostReadPrefix. reflexivity. }
  have Hpc1 : r1 !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b8)).
  { unfold r1, writeSuccess156b4Regs. rewrite lookup_insert.
    rewrite writeSuccess156b4NextPcExact. reflexivity. }
  have Hx1_1 : r1 !! "x1" = Some oldX1.
  { unfold r1. rewrite writeSuccess156b4RegsLookupOther; try discriminate.
    exact Hx1. }
  have Hmstatus1 : eval_a_exp r1 writeSuccess15694Mstatus =
      Some (Val_Bool true).
  { unfold r1, writeSuccess156b4Regs in *.
    cbn. rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate. exact HmstatusAssume. }
  set (o1 := writeSuccess156b8Observations r1 global).
  have Hall1 := segment_156b8_mstatus r1 global oldX1 Hpc1 Hx1_1 Hcodeb8
    Hcodebc Hmstatus1.
  have Hseg1 : IslaInstructionSegment (writeSuccess156b8Before r1 global) o1
      (writeSuccess156bcBefore r2 global).
  { unfold o1, r2, writeSuccess156bcBefore. exact (proj1 Hall1). }
  have Hsilent1 : concat (map microLabels o1) = [] :=
    proj2 (proj2 (proj2 Hall1)).
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
  set (o2 := writeSuccess156bcObservations r2 global).
  have Hall2 := segment_156bc_mstatus r2 global Hpc2 Hx1_2 Hcodebc HcodeInt
    Hmstatus2.
  have Hseg2 : IslaInstructionSegment (writeSuccess156bcBefore r2 global) o2
      (writeSuccess156bcAfter r2 global).
  { unfold o2. exact (proj1 Hall2). }
  have Hsilent2 : concat (map microLabels o2) = [] :=
    proj2 (proj2 (proj2 Hall2)).
  have Hr0 := writeSuccessWithdrawalsRecordedRunZero
    (writeSuccess156b4Before regs global, priorLog).
  have Hr1 := writeSuccessWithdrawalsSilentRecordedSnoc 0 _ [] _ o0 _ Hr0
    Hseg0 Hsilent0.
  have Hr2 := writeSuccessWithdrawalsSilentRecordedSnoc 1 _ [o0] _ o1 _ Hr1
    Hseg1 Hsilent1.
  have Hr3 := writeSuccessWithdrawalsSilentRecordedSnoc 2 _ [o0; o1] _ o2 _ Hr2
    Hseg2 Hsilent2.
  exists [o0; o1; o2]. exact Hr3.
Qed.

Print Assumptions writeSuccessWithdrawals156b4EncoderIntRecordedDirect.
