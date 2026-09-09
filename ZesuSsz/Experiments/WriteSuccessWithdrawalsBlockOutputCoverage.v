From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessStoreOutcome.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputCall.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10194.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1019c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10194Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1019cCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0Coverage.

Import ListNotations.
Open Scope Z_scope.

Definition block_write_output_coverage_statement : Prop :=
  forall data size returnAddress bytes priorLog state segments after,
    Inv_write_output data size returnAddress bytes priorLog state ->
    WriteSuccessWithdrawalsRecordedRun 5 state segments after ->
    exists regs global records,
      state.1 = writeSuccess10190Before regs global /\
      after.1 = writeSuccess101a0After (writeSuccessOutputRegs4 regs) global
        returnAddress /\
      after.2 = priorLog ++ records /\
      records =
        [(SWriteMem (BV 64 0x2401a0c0) (bv_to_bvn data), global.(seq_mem));
         (SWriteMem (BV 64 0x2401a0c8) (bv_to_bvn size), global.(seq_mem))] /\
      writeSuccessOutputRecords data size bytes records.

Lemma writeSuccessOutputRunExact
    (regs : reg_map) (global : seq_global_state)
    (data size returnAddress : bv 64) (returnTrace : isla_trace)
    segments after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10190)) ->
  regs !! "x1" = Some (RVal_Bits returnAddress) ->
  regs !! "x10" = Some (RVal_Bits data) ->
  regs !! "x11" = Some (RVal_Bits size) ->
  bv_extract 0 2 returnAddress = BV 2 0 ->
  global.(seq_instrs) !! returnAddress = Some returnTrace ->
  writeSuccessWithdrawalsInstructionTable global ->
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  set_Forall (fun address =>
    ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
    (dom global.(seq_mem)) ->
  IslaInstructionRun 5 (writeSuccess10190Before regs global) segments after ->
  exists mstatusBits satp result98 result9c,
    segments =
      [writeSuccess10190Observations regs global;
       writeSuccess10194Observations (writeSuccessOutputRegs1 regs) global
         writeSuccess10190Link;
       writeSuccess10198Observations (writeSuccessOutputRegs2 regs) global
         mstatusBits writeSuccessOutputPortBase satp data result98
         WriteSuccessStoreMmio;
       writeSuccess1019cObservations (writeSuccessOutputRegs3 regs) global
         mstatusBits writeSuccessOutputPortBase satp size result9c
         WriteSuccessStoreMmio;
       writeSuccess101a0Observations (writeSuccessOutputRegs4 regs) global
         returnAddress] /\
    after = writeSuccess101a0After (writeSuccessOutputRegs4 regs) global
      returnAddress /\
    segmentRecords (writeSuccess10190Before regs global)
      (flattenMicroObservations segments) =
      [(SWriteMem (BV 64 0x2401a0c0) (bv_to_bvn data), global.(seq_mem));
       (SWriteMem (BV 64 0x2401a0c8) (bv_to_bvn size), global.(seq_mem))].
Proof.
  intros Hpc Hx1 Hx10 Hx11 Halign Hreturn Htable Hfacts Hdom Hrun5.
  destruct (writeSuccessOutputInstructionFacts global Htable) as
    (Hcode90 & Hcode94 & Hcode98 & Hcode9c & Hcodea0).
  destruct (writeSuccessOutputRegisterFacts regs Hfacts) as
    (mstatusBits & satp & oldX5 & Hx5 & HmstatusRoot & Hsatp & Hsys & Hmstatus).
  destruct (writeSuccessOutputCallSegments regs global data size returnAddress
    Hpc Hx1 Hx10 Hx11 Htable Hfacts) as
    (ignoredMstatus & ignoredSatp & _ & _ & _ & _ & _ & Hr2pc & Hr2base &
     Hr2mstatusRoot & Hr2satp & Hr2x10 & Hr2x11 & Hr2x1 & Hr2sys & Hr2mstatus).
  inversion Hrun5 as [|? ? obs90 after90 ? ? Hseg90 Hrun]; subst.
  inversion Hrun as [|? ? obs94 after94 ? ? Hseg94 Hrun']; subst.
  inversion Hrun' as [|? ? obs98 after98 ? ? Hseg98 Hrun'']; subst.
  inversion Hrun'' as [|? ? obs9c after9c ? ? Hseg9c Hruna0]; subst.
  inversion Hruna0 as [|? ? obsa0 aftera0 ? ? Hsega0 Hzero]; subst.
  inversion Hzero; subst.
  destruct (segment_10190_covered regs global oldX5 obs90 after90
    Hpc Hx5 Hcode90 Hcode94 Hmstatus Hseg90) as (Hafter90 & Hobs90).
  subst after90.
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
    rewrite writeSuccess10190RegsLookupOther;
      [exact Hmstatus|congruence|congruence]. }
  destruct (segment_10194_covered (writeSuccessOutputRegs1 regs) global
    writeSuccess10190Link (RVal_Bits writeSuccess10190Link) obs94 after94
    Hr1pc Hr1x5 Hr1x5 Hcode94 Hcode98 Hr1mstatus Hseg94) as
    (Hafter94 & Hobs94).
  subst after94.
  destruct (writeSuccessOutputStoreAssumes (writeSuccessOutputRegs2 regs)
    Hr2base (proj1 (proj2 (proj2 Hr2sys)))
    (proj1 (proj2 (proj2 (proj2 Hr2sys))))) as
    (Ha98 & Hl98 & Hu98 & Ha9c0 & Hl9c0 & Hu9c0).
  destruct (segment_10198_covered (writeSuccessOutputRegs2 regs) global
    ignoredMstatus writeSuccessOutputPortBase ignoredSatp data obs98 after98
    Hr2pc Hr2base Hr2mstatusRoot Hr2satp Hr2x10 Hr2sys Hr2mstatus
    Ha98 Hl98 Hu98 Hcode98 Hcode9c Hseg98) as
    (result98 & outcome98 & Hpermit98 & Hafter98 & Hobs98).
  have Hport98 : writeSuccess10198Address writeSuccessOutputPortBase =
      BV 64 0x2401a0c0 := proj1 writeSuccessOutputPortAddresses.
  have Hmmio98 := writeSuccessOutputMmioPermitted global
    (writeSuccess10198Address writeSuccessOutputPortBase) (or_introl Hport98)
    Hdom.
  have Houtcome98 : outcome98 = WriteSuccessStoreMmio.
  { destruct outcome98; last reflexivity.
    unfold writeSuccessStoreOutcomePermitted in Hpermit98, Hmmio98.
    destruct Hpermit98 as (old & Hread). destruct Hmmio98 as (Hnone & _).
    rewrite Hnone in Hread. discriminate. }
  subst outcome98 after98.
  have Hr3pc : writeSuccessOutputRegs3 regs !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x1019c)).
  { unfold writeSuccessOutputRegs3, writeSuccess10198Regs.
    rewrite lookup_insert writeSuccess10198NextPcExact. reflexivity. }
  have Hr3base : writeSuccessOutputRegs3 regs !! "x5" =
      Some (RVal_Bits writeSuccessOutputPortBase).
  { unfold writeSuccessOutputRegs3. rewrite writeSuccess10198RegsLookupOther;
      [exact Hr2base|congruence]. }
  have Hr3mstatusRoot : writeSuccessOutputRegs3 regs !! "mstatus" =
      Some (RegVal_Struct [("bits", RVal_Bits ignoredMstatus)]).
  { unfold writeSuccessOutputRegs3. rewrite writeSuccess10198RegsLookupOther;
      [exact Hr2mstatusRoot|congruence]. }
  have Hr3satp : writeSuccessOutputRegs3 regs !! "satp" =
      Some (RVal_Bits ignoredSatp).
  { unfold writeSuccessOutputRegs3. rewrite writeSuccess10198RegsLookupOther;
      [exact Hr2satp|congruence]. }
  have Hr3x11 : writeSuccessOutputRegs3 regs !! "x11" = Some (RVal_Bits size).
  { unfold writeSuccessOutputRegs3. rewrite writeSuccess10198RegsLookupOther;
      [exact Hr2x11|congruence]. }
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
    (_ & _ & _ & Ha9c & Hl9c & Hu9c).
  destruct (segment_1019c_covered (writeSuccessOutputRegs3 regs) global
    ignoredMstatus writeSuccessOutputPortBase ignoredSatp size obs9c after9c
    Hr3pc Hr3base Hr3mstatusRoot Hr3satp Hr3x11 Hr3sys Hr3mstatus
    Ha9c Hl9c Hu9c Hcode9c Hcodea0 Hseg9c) as
    (result9c & outcome9c & Hpermit9c & Hafter9c & Hobs9c).
  have Hport9c : writeSuccess1019cAddress writeSuccessOutputPortBase =
      BV 64 0x2401a0c8 := proj2 writeSuccessOutputPortAddresses.
  have Hmmio9c := writeSuccessOutputMmioPermitted global
    (writeSuccess1019cAddress writeSuccessOutputPortBase) (or_intror Hport9c)
    Hdom.
  have Houtcome9c : outcome9c = WriteSuccessStoreMmio.
  { destruct outcome9c; last reflexivity.
    unfold writeSuccessStoreOutcomePermitted in Hpermit9c, Hmmio9c.
    destruct Hpermit9c as (old & Hread). destruct Hmmio9c as (Hnone & _).
    rewrite Hnone in Hread. discriminate. }
  subst outcome9c after9c.
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
  destruct (segment_101a0_covered (writeSuccessOutputRegs4 regs) global
    returnAddress obsa0 after Hr4pc Hr4x1 Hcodea0 Hr4mstatus Hr4align
    Hsega0) as (Haftera0 & Hobsa0).
  subst after.
  subst obs90 obs94 obs98 obs9c obsa0.
  exists ignoredMstatus, ignoredSatp, result98, result9c.
  split; first reflexivity.
  split; first reflexivity.
  cbn [flattenMicroObservations].
  rewrite (segmentRecords_app (writeSuccess10190Before regs global)
    (writeSuccess10190Observations regs global)
    (writeSuccess10190After regs global)).
  2: exact (islaInstructionSegmentCorrespondence _ _ _ Hseg90).
  rewrite (proj1 (writeSuccessOutputSilentRecords regs global
    writeSuccess10190Link returnAddress returnTrace Halign Hreturn)).
  rewrite (segmentRecords_app
    (writeSuccess10194Before (writeSuccessOutputRegs1 regs) global)
    (writeSuccess10194Observations (writeSuccessOutputRegs1 regs) global
      writeSuccess10190Link)
    (writeSuccess10194After (writeSuccessOutputRegs1 regs) global
      writeSuccess10190Link)).
  2: exact (islaInstructionSegmentCorrespondence _ _ _ Hseg94).
  rewrite (proj1 (proj2 (writeSuccessOutputSilentRecords
    (writeSuccessOutputRegs1 regs) global writeSuccess10190Link
    returnAddress returnTrace Halign Hreturn))).
  rewrite (segmentRecords_app
    (writeSuccess10198Before (writeSuccessOutputRegs2 regs) global)
    (writeSuccess10198Observations (writeSuccessOutputRegs2 regs) global
      ignoredMstatus writeSuccessOutputPortBase ignoredSatp data result98
      WriteSuccessStoreMmio)
    (writeSuccess10198After (writeSuccessOutputRegs2 regs) global
      writeSuccessOutputPortBase data WriteSuccessStoreMmio)).
  2: exact (islaInstructionSegmentCorrespondence _ _ _ Hseg98).
  rewrite writeSuccess10198MmioRecords.
  rewrite (segmentRecords_app
    (writeSuccess1019cBefore (writeSuccessOutputRegs3 regs) global)
    (writeSuccess1019cObservations (writeSuccessOutputRegs3 regs) global
      ignoredMstatus writeSuccessOutputPortBase ignoredSatp size result9c
      WriteSuccessStoreMmio)
    (writeSuccess1019cAfter (writeSuccessOutputRegs3 regs) global
      writeSuccessOutputPortBase size WriteSuccessStoreMmio)).
  2: exact (islaInstructionSegmentCorrespondence _ _ _ Hseg9c).
  rewrite writeSuccess1019cMmioRecords.
  rewrite (proj2 (proj2 (writeSuccessOutputSilentRecords
    (writeSuccessOutputRegs4 regs) global writeSuccess10190Link
    returnAddress returnTrace Halign Hreturn))).
  rewrite (proj1 writeSuccessOutputPortAddresses).
  rewrite (proj2 writeSuccessOutputPortAddresses).
  reflexivity.
Qed.

Print Assumptions writeSuccessOutputRunExact.

Lemma block_write_output_covered : block_write_output_coverage_statement.
Proof.
  unfold block_write_output_coverage_statement.
  intros data size returnAddress bytes priorLog state segments after
    Hinv Hrecorded.
  destruct Hrecorded as (Hrun & HafterLog).
  destruct state as [[local global] log].
  destruct local as [trace regs pcRegister nb]. cbn in Hinv, Hrun,
    HafterLog |- *.
  destruct Hinv as
    (Hboundary & HpcRegister & HconcretePc & Hx1 & Hx10 & Hx11 &
     HreturnAlign & HreturnCode & Hsize & Hread & Htable & HregisterFacts &
     HmemoryDom & Hlog).
  cbn in HpcRegister, Hlog, HreturnCode, Htable, HregisterFacts,
    HmemoryDom, Hx1, Hx10, Hx11, Hread, HconcretePc.
  subst pcRegister log.
  destruct HreturnCode as (returnTrace & HreturnLookup).
  destruct Hboundary as (Hnb & pc & source & Hpc & Hsource & Htrace).
  cbn in Hnb, Hpc, Hsource, Htrace, HconcretePc.
  subst nb trace.
  change (match regs !! "PC" with
    | Some (RVal_Bits value) => Some (bvn_unsigned value)
    | _ => None
    end = Some 0x10190) in HconcretePc.
  rewrite Hpc in HconcretePc. inversion HconcretePc as [Hunsigned].
  change (bv_unsigned pc = 0x10190) in Hunsigned.
  have Hpceq : pc = Z_to_bv 64 0x10190.
  { rewrite <- (Z_to_bv_bv_unsigned 64 pc). rewrite Hunsigned. reflexivity. }
  subst pc.
  have Hcode90 := proj1 (writeSuccessOutputInstructionFacts global Htable).
  rewrite Hsource in Hcode90. inversion Hcode90. subst source.
  destruct (writeSuccessOutputRunExact regs global data size returnAddress
    returnTrace segments after.1 Hpc Hx1 Hx10 Hx11 HreturnAlign
    HreturnLookup Htable HregisterFacts HmemoryDom Hrun) as
    (mstatusBits & satp & result98 & result9c & Hsegments & Hfinal &
     HsegmentRecords).
  set (records :=
    [(SWriteMem (BV 64 0x2401a0c0) (bv_to_bvn data), global.(seq_mem));
     (SWriteMem (BV 64 0x2401a0c8) (bv_to_bvn size), global.(seq_mem))]).
  exists regs, global, records. split; first reflexivity.
  split; first exact Hfinal.
  split.
  - unfold records. rewrite HafterLog HsegmentRecords. reflexivity.
  - split; first reflexivity.
    unfold records, writeSuccessOutputRecords. split.
    + unfold WriteSuccessOutputSemantic.writeOutputDescriptorEvents.
      reflexivity.
    + cbn. rewrite bool_decide_true; last (split; bv_solve).
      unfold bvn_unsigned.
      have Hsize' : bv_unsigned (bvn_val (bv_to_bvn size)) =
          Z.of_nat (length bytes).
      { cbn. exact Hsize. }
      rewrite Hsize'. cbn.
      replace (Z.to_N (Z.of_nat (length bytes))) with
        (N.of_nat (length bytes)) by lia.
      rewrite Hread. reflexivity.
Qed.

Print Assumptions block_write_output_covered.
