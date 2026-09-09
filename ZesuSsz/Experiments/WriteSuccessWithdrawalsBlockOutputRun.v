From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessStoreOutcome.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputPhases.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10194.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1019c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.
Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessOutputRecordedComposition
    (regs : reg_map) (global : seq_global_state)
    (data size returnAddress : bv 64) (bytes : list (bv 8))
    (priorLog : list WriteSuccessWithdrawalsRecord) (returnTrace : isla_trace) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10190)) ->
  regs !! "x1" = Some (RVal_Bits returnAddress) ->
  regs !! "x10" = Some (RVal_Bits data) ->
  regs !! "x11" = Some (RVal_Bits size) ->
  bv_extract 0 2 returnAddress = BV 2 0 ->
  global.(seq_instrs) !! returnAddress = Some returnTrace ->
  bv_unsigned size = Z.of_nat (length bytes) ->
  read_mem_list global.(seq_mem) (bv_unsigned data)
    (N.of_nat (length bytes)) = Some bytes ->
  writeSuccessWithdrawalsInstructionTable global ->
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  set_Forall (fun address =>
    ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
    (dom global.(seq_mem)) ->
  exists segments finalMachine records,
    WriteSuccessWithdrawalsRecordedRun 5
      (writeSuccess10190Before regs global, priorLog) segments
      (finalMachine, priorLog ++ records) /\
    writeSuccessWithdrawalsConcretePc
      (finalMachine, priorLog ++ records) = Some (bv_unsigned returnAddress) /\
    writeSuccessOutputRecords data size bytes records.
Proof.
  intros Hpc Hx1 Hx10 Hx11 HreturnAlign HreturnLookup Hsize Hread Htable
    HregisterFacts HmemoryDom.
  destruct (writeSuccessOutputPhases regs global data size returnAddress
    Hpc Hx1 Hx10 Hx11 HreturnAlign Htable HregisterFacts HmemoryDom) as
    (mstatusBits & satp & Hseg90 & Hseg94 & Hseg98 & Hseg9c & Hsega0).
  set (segments :=
    [writeSuccess10190Observations regs global;
     writeSuccess10194Observations (writeSuccessOutputRegs1 regs) global
       writeSuccess10190Link;
     writeSuccess10198Observations (writeSuccessOutputRegs2 regs) global
       mstatusBits writeSuccessOutputPortBase satp data false
       WriteSuccessStoreMmio;
     writeSuccess1019cObservations (writeSuccessOutputRegs3 regs) global
       mstatusBits writeSuccessOutputPortBase satp size false
       WriteSuccessStoreMmio;
     writeSuccess101a0Observations (writeSuccessOutputRegs4 regs) global
       returnAddress]).
  set (records :=
    [(SWriteMem (BV 64 0x2401a0c0) (bv_to_bvn data), global.(seq_mem));
     (SWriteMem (BV 64 0x2401a0c8) (bv_to_bvn size), global.(seq_mem))]).
  set (finalMachine := writeSuccess101a0After
    (writeSuccessOutputRegs4 regs) global returnAddress).
  have Hr0 := writeSuccessWithdrawalsRecordedRunZero
    (writeSuccess10190Before regs global, priorLog).
  have Hr90 := writeSuccessWithdrawalsRecordedRunSnoc 0
    (writeSuccess10190Before regs global, priorLog) []
    (writeSuccess10190Before regs global, priorLog)
    (writeSuccess10190Observations regs global)
    (writeSuccess10190After regs global) Hr0 Hseg90.
  rewrite (proj1 (writeSuccessOutputSilentRecords regs global
    writeSuccess10190Link returnAddress returnTrace HreturnAlign
    HreturnLookup)) in Hr90. rewrite app_nil_r in Hr90.
  have Hr94 := writeSuccessWithdrawalsRecordedRunSnoc 1
    (writeSuccess10190Before regs global, priorLog)
    [writeSuccess10190Observations regs global]
    (writeSuccess10194Before (writeSuccessOutputRegs1 regs) global, priorLog)
    (writeSuccess10194Observations (writeSuccessOutputRegs1 regs) global
      writeSuccess10190Link)
    (writeSuccess10194After (writeSuccessOutputRegs1 regs) global
      writeSuccess10190Link) Hr90 Hseg94.
  rewrite (proj1 (proj2 (writeSuccessOutputSilentRecords
    (writeSuccessOutputRegs1 regs) global writeSuccess10190Link
    returnAddress returnTrace HreturnAlign HreturnLookup))) in Hr94. rewrite app_nil_r in Hr94.
  have Hr98 := writeSuccessWithdrawalsRecordedRunSnoc 2
    (writeSuccess10190Before regs global, priorLog)
    [writeSuccess10190Observations regs global;
     writeSuccess10194Observations (writeSuccessOutputRegs1 regs) global
       writeSuccess10190Link]
    (writeSuccess10198Before (writeSuccessOutputRegs2 regs) global, priorLog)
    (writeSuccess10198Observations (writeSuccessOutputRegs2 regs) global
      mstatusBits writeSuccessOutputPortBase satp data false WriteSuccessStoreMmio)
    (writeSuccess10198After (writeSuccessOutputRegs2 regs) global
      writeSuccessOutputPortBase data WriteSuccessStoreMmio) Hr94 Hseg98.
  rewrite writeSuccess10198MmioRecords in Hr98. cbn in Hr98.
  have Hr9c := writeSuccessWithdrawalsRecordedRunSnoc 3
    (writeSuccess10190Before regs global, priorLog)
    [writeSuccess10190Observations regs global;
     writeSuccess10194Observations (writeSuccessOutputRegs1 regs) global
       writeSuccess10190Link;
     writeSuccess10198Observations (writeSuccessOutputRegs2 regs) global
       mstatusBits writeSuccessOutputPortBase satp data false WriteSuccessStoreMmio]
    (writeSuccess1019cBefore (writeSuccessOutputRegs3 regs) global,
      priorLog ++ [(SWriteMem (writeSuccess10198Address writeSuccessOutputPortBase)
        (bv_to_bvn data), global.(seq_mem))])
    (writeSuccess1019cObservations (writeSuccessOutputRegs3 regs) global
      mstatusBits writeSuccessOutputPortBase satp size false WriteSuccessStoreMmio)
    (writeSuccess1019cAfter (writeSuccessOutputRegs3 regs) global
      writeSuccessOutputPortBase size WriteSuccessStoreMmio) Hr98 Hseg9c.
  rewrite writeSuccess1019cMmioRecords in Hr9c.
  cbn in Hr9c.
  have Hrecorded := writeSuccessWithdrawalsRecordedRunSnoc 4
    (writeSuccess10190Before regs global, priorLog)
    [writeSuccess10190Observations regs global;
     writeSuccess10194Observations (writeSuccessOutputRegs1 regs) global
       writeSuccess10190Link;
     writeSuccess10198Observations (writeSuccessOutputRegs2 regs) global
       mstatusBits writeSuccessOutputPortBase satp data false WriteSuccessStoreMmio;
     writeSuccess1019cObservations (writeSuccessOutputRegs3 regs) global
       mstatusBits writeSuccessOutputPortBase satp size false WriteSuccessStoreMmio]
    (writeSuccess101a0Before (writeSuccessOutputRegs4 regs) global,
      (priorLog ++
       [(SWriteMem (writeSuccess10198Address writeSuccessOutputPortBase)
           (bv_to_bvn data), global.(seq_mem))]) ++
      [(SWriteMem (writeSuccess1019cAddress writeSuccessOutputPortBase)
          (bv_to_bvn size), global.(seq_mem))])
    (writeSuccess101a0Observations (writeSuccessOutputRegs4 regs) global
      returnAddress) finalMachine Hr9c Hsega0.
  rewrite (proj2 (proj2 (writeSuccessOutputSilentRecords
    (writeSuccessOutputRegs4 regs) global writeSuccess10190Link
    returnAddress returnTrace HreturnAlign HreturnLookup))) in Hrecorded.
  rewrite app_nil_r in Hrecorded.
  have Hlogs :
      (priorLog ++
       [(SWriteMem (writeSuccess10198Address writeSuccessOutputPortBase)
           (bv_to_bvn data), global.(seq_mem))]) ++
      [(SWriteMem (writeSuccess1019cAddress writeSuccessOutputPortBase)
          (bv_to_bvn size), global.(seq_mem))] =
      priorLog ++
      [(SWriteMem (writeSuccess10198Address writeSuccessOutputPortBase)
          (bv_to_bvn data), global.(seq_mem));
       (SWriteMem (writeSuccess1019cAddress writeSuccessOutputPortBase)
          (bv_to_bvn size), global.(seq_mem))].
  { rewrite <- app_assoc. reflexivity. }
  rewrite Hlogs in Hrecorded.
  have Hport98 := proj1 writeSuccessOutputPortAddresses.
  have Hport9c := proj2 writeSuccessOutputPortAddresses.
  rewrite Hport98 Hport9c in Hrecorded.
  unfold records.
  exists segments, finalMachine,
    [(SWriteMem (BV 64 0x2401a0c0) (bv_to_bvn data), global.(seq_mem));
     (SWriteMem (BV 64 0x2401a0c8) (bv_to_bvn size), global.(seq_mem))].
  split; first exact Hrecorded. split.
  - unfold finalMachine, writeSuccessWithdrawalsConcretePc,
      writeSuccess101a0After. cbn.
    rewrite (writeSuccessOutputReturnTargetExact returnAddress HreturnAlign). rewrite HreturnLookup. cbn. unfold writeSuccess101a0Regs. rewrite lookup_insert. rewrite (writeSuccessOutputReturnTargetExact returnAddress HreturnAlign). reflexivity.
  - unfold writeSuccessOutputRecords. split.
    + unfold WriteSuccessOutputSemantic.writeOutputDescriptorEvents. reflexivity.
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

Print Assumptions writeSuccessOutputRecordedComposition.
