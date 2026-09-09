From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_01.a10198.
Require Import IslaTraces.write_success_01.a1019c.
Require Import IslaTraces.write_success_01.a101a0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10194.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1019c.
Import ListNotations.
Open Scope Z_scope.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.

Definition writeSuccessOutputCallSegmentsStatement : Prop :=
  forall regs global data size returnAddress,
    regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10190)) ->
    regs !! "x1" = Some (RVal_Bits returnAddress) ->
    regs !! "x10" = Some (RVal_Bits data) ->
    regs !! "x11" = Some (RVal_Bits size) ->
    writeSuccessWithdrawalsInstructionTable global ->
    writeSuccessWithdrawalsOperationalRegisterFacts regs ->
    exists (mstatusBits satp : bv 64),
      IslaInstructionSegment (writeSuccess10190Before regs global)
        (writeSuccess10190Observations regs global)
        (writeSuccess10190After regs global) /\
      IslaInstructionSegment
        (writeSuccess10194Before (writeSuccessOutputRegs1 regs) global)
        (writeSuccess10194Observations (writeSuccessOutputRegs1 regs) global
          writeSuccess10190Link)
        (writeSuccess10194After (writeSuccessOutputRegs1 regs) global
          writeSuccess10190Link) /\
      global.(seq_instrs) !! Z_to_bv 64 0x10198 = Some a10198 /\
      global.(seq_instrs) !! Z_to_bv 64 0x1019c = Some a1019c /\
      global.(seq_instrs) !! Z_to_bv 64 0x101a0 = Some a101a0 /\
      writeSuccessOutputRegs2 regs !! "PC" =
        Some (RVal_Bits (Z_to_bv 64 0x10198)) /\
      writeSuccessOutputRegs2 regs !! "x5" =
        Some (RVal_Bits writeSuccessOutputPortBase) /\
      writeSuccessOutputRegs2 regs !! "mstatus" =
        Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) /\
      writeSuccessOutputRegs2 regs !! "satp" = Some (RVal_Bits satp) /\
      writeSuccessOutputRegs2 regs !! "x10" = Some (RVal_Bits data) /\
      writeSuccessOutputRegs2 regs !! "x11" = Some (RVal_Bits size) /\
      writeSuccessOutputRegs2 regs !! "x1" = Some (RVal_Bits returnAddress) /\
      writeSuccess10198SysRegs (writeSuccessOutputRegs2 regs) /\
      eval_a_exp (writeSuccessOutputRegs2 regs) writeSuccess15694Mstatus =
        Some (Val_Bool true).

Lemma writeSuccessOutputCallSegments : writeSuccessOutputCallSegmentsStatement.
Proof.
  unfold writeSuccessOutputCallSegmentsStatement.
  intros regs global data size returnAddress Hpc Hx1 Hx10 Hx11 Htable Hfacts.
  destruct (writeSuccessOutputInstructionFacts global Htable) as
    (Hcode90 & Hcode94 & Hcode98 & Hcode9c & Hcodea0).
  destruct (writeSuccessOutputRegisterFacts regs Hfacts) as
    (mstatusBits & satp & oldX5 & Hx5 & HmstatusRoot & Hsatp & Hsys & Hmstatus).
  have Hseg90 := proj1 (segment_10190 regs global oldX5
    Hpc Hx5 Hcode90 Hcode94 Hmstatus).
  have Hr1pc : writeSuccessOutputRegs1 regs !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x10194)).
  { unfold writeSuccessOutputRegs1, writeSuccess10190Regs.
    rewrite lookup_insert writeSuccess10190NextPcExact. reflexivity. }
  have Hr1x5 : writeSuccessOutputRegs1 regs !! "x5" =
      Some (RVal_Bits writeSuccess10190Link).
  { unfold writeSuccessOutputRegs1, writeSuccess10190Regs.
    rewrite lookup_insert_ne; last congruence. rewrite lookup_insert. reflexivity. }
  have Hr1mstatus : eval_a_exp (writeSuccessOutputRegs1 regs)
      writeSuccess10194Mstatus = Some (Val_Bool true).
  { unfold writeSuccessOutputRegs1, writeSuccess10194Mstatus,
      writeSuccess15694Mstatus in Hmstatus |- *. cbn in Hmstatus |- *.
    rewrite writeSuccess10190RegsLookupOther; [exact Hmstatus|congruence|congruence]. }
  have Hseg94 := proj1 (segment_10194 (writeSuccessOutputRegs1 regs) global
    writeSuccess10190Link (RVal_Bits writeSuccess10190Link)
    Hr1pc Hr1x5 Hr1x5 Hcode94 Hcode98 Hr1mstatus).
  have Hr2pc : writeSuccessOutputRegs2 regs !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x10198)).
  { unfold writeSuccessOutputRegs2, writeSuccess10194Regs.
    rewrite lookup_insert writeSuccess10194NextPcExact. reflexivity. }
  have Hr2base := writeSuccessOutputRegs2Base regs.
  have Hr2mstatusRoot : writeSuccessOutputRegs2 regs !! "mstatus" =
      Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]).
  { rewrite writeSuccessOutputRegs2LookupOther; congruence. }
  have Hr2satp : writeSuccessOutputRegs2 regs !! "satp" = Some (RVal_Bits satp).
  { rewrite writeSuccessOutputRegs2LookupOther; congruence. }
  have Hr2x10 : writeSuccessOutputRegs2 regs !! "x10" = Some (RVal_Bits data).
  { rewrite writeSuccessOutputRegs2LookupOther; congruence. }
  have Hr2x11 : writeSuccessOutputRegs2 regs !! "x11" = Some (RVal_Bits size).
  { rewrite writeSuccessOutputRegs2LookupOther; congruence. }
  have Hr2x1 : writeSuccessOutputRegs2 regs !! "x1" = Some (RVal_Bits returnAddress).
  { rewrite writeSuccessOutputRegs2LookupOther; congruence. }
  have Hr2sys : writeSuccess10198SysRegs (writeSuccessOutputRegs2 regs).
  { unfold writeSuccess10198SysRegs in Hsys |- *.
    destruct Hsys as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
    repeat split; rewrite writeSuccessOutputRegs2LookupOther;
      try congruence; assumption. }
  have Hr2mstatus : eval_a_exp (writeSuccessOutputRegs2 regs)
      writeSuccess15694Mstatus = Some (Val_Bool true).
  { unfold writeSuccess15694Mstatus in Hmstatus |- *. cbn in Hmstatus |- *.
    rewrite writeSuccessOutputRegs2LookupOther; [exact Hmstatus|congruence|congruence]. }
  exists mstatusBits, satp. repeat split; try assumption;
    unfold writeSuccess10198SysRegs in Hr2sys; tauto.
Qed.

Print Assumptions writeSuccessOutputCallSegments.
