From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_91.a156a8.
Require Import IslaTraces.write_success_91.a156ac.
Require Import IslaTraces.write_success_91.a156b0.
Require Import IslaTraces.write_success_07.a15d10.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156ac.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b0.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.

Import ListNotations.

Lemma writeSuccessWithdrawals156a8EncoderIntRecordedDirect regs global sp pointer
    current withdrawal priorLog (mstatusBits satp oldDest : bv 64)
    (oldX1 : valu) :
  writeSuccessWithdrawals156a8Regs regs global sp pointer current !! "PC" =
    Some (RVal_Bits (Z_to_bv 64 0x156a8)) ->
  writeSuccessWithdrawals156a8Regs regs global sp pointer current !! "x2" =
    Some (RVal_Bits sp) ->
  writeSuccessWithdrawals156a8Regs regs global sp pointer current !! "mstatus" =
    Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  writeSuccessWithdrawals156a8Regs regs global sp pointer current !! "satp" =
    Some (RVal_Bits satp) ->
  writeSuccessWithdrawals156a8Regs regs global sp pointer current !! "x10" =
    Some (RVal_Bits oldDest) ->
  writeSuccessWithdrawals156a8Regs regs global sp pointer current !! "x1" =
    Some oldX1 ->
  writeSuccess156a8SysRegs
    (writeSuccessWithdrawals156a8Regs regs global sp pointer current) ->
  eval_a_exp (writeSuccessWithdrawals156a8Regs regs global sp pointer current)
    writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp (writeSuccessWithdrawals156a8Regs regs global sp pointer current)
    writeSuccess156a8Aligned = Some (Val_Bool true) ->
  eval_a_exp (writeSuccessWithdrawals156a8Regs regs global sp pointer current)
    writeSuccess156a8Lower = Some (Val_Bool true) ->
  eval_a_exp (writeSuccessWithdrawals156a8Regs regs global sp pointer current)
    writeSuccess156a8Upper = Some (Val_Bool true) ->
  read_mem (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_mem)
    (bv_unsigned (writeSuccess156a8Address sp)) 8 =
    Some (bv_to_bvn (writeSuccessWithdrawalsIndexValue withdrawal)) ->
  writeSuccessWithdrawalsInstructionTable global ->
  exists segments,
    WriteSuccessWithdrawalsRecordedRun 3
      (writeSuccessWithdrawals156a8State regs global sp pointer current, priorLog)
      segments
      (writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer current
        withdrawal, priorLog).
Proof.
  intros Hpc Hsp Hmstatus Hsatp Hdest Hx1 Hsys HmstatusAssume Haligned Hlower
    Hupper Hread Htable.
  have Hcodea8 :
      (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_instrs)
        !! Z_to_bv 64 0x156a8 = Some a156a8.
  { rewrite writeSuccessWithdrawals156a8Instrs. apply Htable.
    unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hcodeac :
      (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_instrs)
        !! Z_to_bv 64 0x156ac = Some a156ac.
  { rewrite writeSuccessWithdrawals156a8Instrs. apply Htable.
    unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hcodeb0 :
      (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_instrs)
        !! Z_to_bv 64 0x156b0 = Some a156b0.
  { rewrite writeSuccessWithdrawals156a8Instrs. apply Htable.
    unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have HcodeInt :
      (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_instrs)
        !! Z_to_bv 64 0x15d10 = Some a15d10.
  { rewrite writeSuccessWithdrawals156a8Instrs. apply Htable.
    unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  set (r0 := writeSuccessWithdrawals156a8Regs regs global sp pointer current).
  set (g0 := writeSuccessWithdrawals156a8Global regs global sp pointer current).
  set (value := writeSuccessWithdrawalsIndexValue withdrawal).
  set (o0 := writeSuccess156a8Observations r0 g0 mstatusBits sp satp value).
  have Hall0 := segment_156a8 r0 g0 mstatusBits sp satp value oldDest Hpc Hsp
    Hmstatus Hsatp Hdest Hsys HmstatusAssume Haligned Hlower Hupper Hread
    Hcodea8 Hcodeac.
  have Hseg0 : IslaInstructionSegment (writeSuccessWithdrawals156a8State regs
      global sp pointer current) o0
      (writeSuccessWithdrawals156acState regs global sp pointer current withdrawal).
  { unfold writeSuccessWithdrawals156a8State, writeSuccessWithdrawals156acState,
      o0, r0, g0, value. exact (proj1 Hall0). }
  have Hsilent0 : concat (map microLabels o0) = [].
  { unfold o0, writeSuccess156a8Observations,
      writeSuccess156a8PrefixObservations,
      writeSuccess156a8ExecutionPrefix,
      writeSuccess156a8PreReadObservations,
      writeSuccess156a8PostReadPrefix. reflexivity. }
  set (s1 := writeSuccessWithdrawals156acState regs global sp pointer current
    withdrawal).
  have Hpc1 := writeSuccessWithdrawals156acPc regs global sp pointer current
    withdrawal.
  have Hx1_1 := writeSuccessWithdrawals156acX1 regs global sp pointer current
    withdrawal oldX1 Hx1.
  have Hmstatus1 := writeSuccessWithdrawals156acMstatus regs global sp pointer
    current withdrawal HmstatusAssume.
  set (o1 := writeSuccess156acObservations s1.1.(seq_regs) s1.2).
  have Hall1 := segment_156ac_mstatus s1.1.(seq_regs) s1.2 oldX1 Hpc1 Hx1_1
    Hcodeac Hcodeb0 Hmstatus1.
  have Hseg1 : IslaInstructionSegment s1 o1
      (writeSuccessWithdrawals156b0State regs global sp pointer current withdrawal).
  { unfold s1, o1, writeSuccessWithdrawals156b0State,
      writeSuccessWithdrawals156acState. exact (proj1 Hall1). }
  have Hsilent1 : concat (map microLabels o1) = [] :=
    proj2 (proj2 (proj2 Hall1)).
  set (s2 := writeSuccessWithdrawals156b0State regs global sp pointer current
    withdrawal).
  have Hpc2 := writeSuccessWithdrawals156b0Pc regs global sp pointer current
    withdrawal.
  have Hx1_2 := writeSuccessWithdrawals156b0X1 regs global sp pointer current
    withdrawal.
  have Hmstatus2 := writeSuccessWithdrawals156b0Mstatus regs global sp pointer
    current withdrawal HmstatusAssume.
  set (o2 := writeSuccess156b0Observations s2.1.(seq_regs) s2.2).
  have Hall2 := segment_156b0_mstatus s2.1.(seq_regs) s2.2 Hpc2 Hx1_2
    Hcodeb0 HcodeInt Hmstatus2.
  have Hseg2 : IslaInstructionSegment s2 o2
      (writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer current
        withdrawal).
  { unfold s2, o2, writeSuccessWithdrawalsEncoderInt156b4State,
      writeSuccessWithdrawals156b0State. exact (proj1 Hall2). }
  have Hsilent2 : concat (map microLabels o2) = [] :=
    proj2 (proj2 (proj2 Hall2)).
  have Hr0 := writeSuccessWithdrawalsRecordedRunZero
    (writeSuccessWithdrawals156a8State regs global sp pointer current, priorLog).
  have Hr1 := writeSuccessWithdrawalsSilentRecordedSnoc 0 _ [] _ o0 _ Hr0
    Hseg0 Hsilent0.
  have Hr2 := writeSuccessWithdrawalsSilentRecordedSnoc 1 _ [o0] _ o1 _ Hr1
    Hseg1 Hsilent1.
  have Hr3 := writeSuccessWithdrawalsSilentRecordedSnoc 2 _ [o0; o1] _ o2 _ Hr2
    Hseg2 Hsilent2.
  exists [o0; o1; o2]. exact Hr3.
Qed.

Print Assumptions writeSuccessWithdrawals156a8EncoderIntRecordedDirect.
