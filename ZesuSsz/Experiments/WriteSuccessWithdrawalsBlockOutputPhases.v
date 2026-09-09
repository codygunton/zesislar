From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessStoreOutcome.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputCall.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10194.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1019c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.
Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessOutputPhasesStatement : Prop :=
  forall (regs : reg_map) (global : seq_global_state) (data size returnAddress : bv 64),
    regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10190)) ->
    regs !! "x1" = Some (RVal_Bits returnAddress) ->
    regs !! "x10" = Some (RVal_Bits data) ->
    regs !! "x11" = Some (RVal_Bits size) ->
    bv_extract 0 2 returnAddress = BV 2 0 ->
    writeSuccessWithdrawalsInstructionTable global ->
    writeSuccessWithdrawalsOperationalRegisterFacts regs ->
    set_Forall (fun address =>
      ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
      (dom global.(seq_mem)) ->
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
      IslaInstructionSegment
        (writeSuccess10198Before (writeSuccessOutputRegs2 regs) global)
        (writeSuccess10198Observations (writeSuccessOutputRegs2 regs) global
          mstatusBits writeSuccessOutputPortBase satp data false
          WriteSuccessStoreMmio)
        (writeSuccess10198After (writeSuccessOutputRegs2 regs) global
          writeSuccessOutputPortBase data WriteSuccessStoreMmio) /\
      IslaInstructionSegment
        (writeSuccess1019cBefore (writeSuccessOutputRegs3 regs) global)
        (writeSuccess1019cObservations (writeSuccessOutputRegs3 regs) global
          mstatusBits writeSuccessOutputPortBase satp size false
          WriteSuccessStoreMmio)
        (writeSuccess1019cAfter (writeSuccessOutputRegs3 regs) global
          writeSuccessOutputPortBase size WriteSuccessStoreMmio) /\
      IslaInstructionSegment
        (writeSuccess101a0Before (writeSuccessOutputRegs4 regs) global)
        (writeSuccess101a0Observations (writeSuccessOutputRegs4 regs) global
          returnAddress)
        (writeSuccess101a0After (writeSuccessOutputRegs4 regs) global
          returnAddress).

Lemma writeSuccessOutputPhases : writeSuccessOutputPhasesStatement.
Proof.
  unfold writeSuccessOutputPhasesStatement.
  intros regs global data size returnAddress Hpc Hx1 Hx10 Hx11 HreturnAlign
    Htable HregisterFacts HmemoryDom.
  destruct (writeSuccessOutputCallSegments regs global data size returnAddress
    Hpc Hx1 Hx10 Hx11 Htable HregisterFacts) as
    (mstatusBits & satp & Hseg90 & Hseg94 & Hcode98 & Hcode9c & Hcodea0 &
     Hr2pc & Hr2base & Hr2mstatusRoot & Hr2satp & Hr2x10 & Hr2x11 & Hr2x1 &
     Hr2sys & Hr2mstatus).
  destruct (writeSuccessOutputStoreAssumes (writeSuccessOutputRegs2 regs)
    Hr2base (proj1 (proj2 (proj2 Hr2sys)))
    (proj1 (proj2 (proj2 (proj2 Hr2sys))))) as
    (Halign98 & Hlower98 & Hupper98 & Halign9c & Hlower9c & Hupper9c).
  have Hport98 : writeSuccess10198Address writeSuccessOutputPortBase =
      BV 64 0x2401a0c0 := proj1 writeSuccessOutputPortAddresses.
  have Hmmio98 := writeSuccessOutputMmioPermitted global
    (writeSuccess10198Address writeSuccessOutputPortBase) (or_introl Hport98)
    HmemoryDom.
  have Hseg98 := proj1 (segment_10198 (writeSuccessOutputRegs2 regs) global
    mstatusBits writeSuccessOutputPortBase satp data false
    WriteSuccessStoreMmio Hr2pc Hr2base Hr2mstatusRoot Hr2satp Hr2x10 Hr2sys
    Hr2mstatus Halign98 Hlower98 Hupper98 Hmmio98 Hcode98 Hcode9c).
  have Hr3pc : writeSuccessOutputRegs3 regs !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x1019c)).
  { unfold writeSuccessOutputRegs3, writeSuccess10198Regs.
    rewrite lookup_insert writeSuccess10198NextPcExact. reflexivity. }
  have Hr3base : writeSuccessOutputRegs3 regs !! "x5" =
      Some (RVal_Bits writeSuccessOutputPortBase).
  { unfold writeSuccessOutputRegs3. rewrite writeSuccess10198RegsLookupOther;
      [exact Hr2base|congruence]. }
  have Hr3mstatusRoot : writeSuccessOutputRegs3 regs !! "mstatus" =
      Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]).
  { unfold writeSuccessOutputRegs3. rewrite writeSuccess10198RegsLookupOther; [assumption|congruence]. }
  have Hr3satp : writeSuccessOutputRegs3 regs !! "satp" = Some (RVal_Bits satp).
  { unfold writeSuccessOutputRegs3. rewrite writeSuccess10198RegsLookupOther; [assumption|congruence]. }
  have Hr3x11 : writeSuccessOutputRegs3 regs !! "x11" =
      Some (RVal_Bits size).
  { unfold writeSuccessOutputRegs3. rewrite writeSuccess10198RegsLookupOther; [assumption|congruence]. }
  have Hr3sys : writeSuccess1019cSysRegs (writeSuccessOutputRegs3 regs).
  { unfold writeSuccess1019cSysRegs, writeSuccess10198SysRegs in Hr2sys |- *.
    destruct Hr2sys as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
    repeat split; rewrite writeSuccess10198RegsLookupOther;
      try congruence; assumption. }
  have Hr3mstatus : eval_a_exp (writeSuccessOutputRegs3 regs)
      writeSuccess15694Mstatus = Some (Val_Bool true).
  { unfold writeSuccessOutputRegs3, writeSuccess15694Mstatus in Hr2mstatus |- *.
    cbn in Hr2mstatus |- *. rewrite writeSuccess10198RegsLookupOther;
      [exact Hr2mstatus|congruence]. }
  destruct (writeSuccessOutputStoreAssumes (writeSuccessOutputRegs3 regs)
    Hr3base (proj1 (proj2 (proj2 Hr3sys)))
    (proj1 (proj2 (proj2 (proj2 Hr3sys))))) as
    (_ & _ & _ & Hr3align9c & Hr3lower9c & Hr3upper9c).
  have Hport9c : writeSuccess1019cAddress writeSuccessOutputPortBase =
      BV 64 0x2401a0c8 := proj2 writeSuccessOutputPortAddresses.
  have Hmmio9c := writeSuccessOutputMmioPermitted global
    (writeSuccess1019cAddress writeSuccessOutputPortBase) (or_intror Hport9c)
    HmemoryDom.
  have Hseg9c := proj1 (segment_1019c (writeSuccessOutputRegs3 regs) global
    mstatusBits writeSuccessOutputPortBase satp size false
    WriteSuccessStoreMmio Hr3pc Hr3base Hr3mstatusRoot Hr3satp Hr3x11 Hr3sys
    Hr3mstatus Hr3align9c Hr3lower9c Hr3upper9c Hmmio9c Hcode9c Hcodea0).
  have Hr4pc : writeSuccessOutputRegs4 regs !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x101a0)).
  { unfold writeSuccessOutputRegs4, writeSuccess1019cRegs.
    rewrite lookup_insert writeSuccess1019cNextPcExact. reflexivity. }
  have Hr4x1 : writeSuccessOutputRegs4 regs !! "x1" =
      Some (RVal_Bits returnAddress).
  { rewrite writeSuccessOutputRegs4LookupOther; congruence. }
  have Hr4mstatus : eval_a_exp (writeSuccessOutputRegs4 regs)
      writeSuccess15694Mstatus = Some (Val_Bool true).
  { unfold writeSuccessOutputRegs4, writeSuccess15694Mstatus in Hr3mstatus |- *.
    cbn in Hr3mstatus |- *. rewrite writeSuccess1019cRegsLookupOther;
      [exact Hr3mstatus|congruence]. }
  have Hr4align : eval_a_exp (writeSuccessOutputRegs4 regs)
      writeSuccess101a0Alignment = Some (Val_Bool true).
  { apply (writeSuccessOutputReturnAlignmentEval _ returnAddress); assumption. }
  have Hsega0 := proj1 (segment_101a0 (writeSuccessOutputRegs4 regs) global
    returnAddress Hr4pc Hr4x1 Hcodea0 Hr4mstatus Hr4align).
  exists mstatusBits, satp. repeat split; assumption.
Qed.

Print Assumptions writeSuccessOutputPhases.
