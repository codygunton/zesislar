From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d2c.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntPositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntPrefixPositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntOutputPositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntSuffixPositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedRunSplit.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntPrefixRecordedPositions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputRecordedPositions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntFrame.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSuffix.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2c.

Import ListNotations.
Open Scope Z_scope.

Theorem writeSuccessWithdrawalsEncoderIntActualPositions remaining start
    (regs : reg_map) (global : seq_global_state)
    (value sp returnAddress : bv 64) scratch memoryFrame
    (returnTrace : isla_trace) priorLog segments after :
  writeSuccessWithdrawalsEncoderIntPositionStart start returnAddress ->
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d10)) ->
  regs !! "x1" = Some (RVal_Bits returnAddress) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some (RVal_Bits value) ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  bv_extract 0 2 returnAddress = BV 2 0 ->
  global.(seq_instrs) !! returnAddress = Some returnTrace ->
  bv_unsigned sp `mod` 8 = 0 ->
  0x20000000 <= bv_unsigned sp - 16 ->
  bv_unsigned sp <= 0x40000000 ->
  read_mem_list global.(seq_mem) (bv_unsigned sp - 16) 16%N = Some scratch ->
  islaMemoryRange (bv_unsigned sp - 16) 16 ->
  (forall location,
    bv_unsigned sp - 16 <= location < bv_unsigned sp ->
    is_Some (global.(seq_mem) !! Z_to_bv 64 location)) ->
  writeSuccessMemoryRangeFrame (bv_unsigned sp - 16) 16
    global.(seq_mem) memoryFrame ->
  writeSuccessWithdrawalsInstructionTable global ->
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  set_Forall (fun address =>
    ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
    (dom global.(seq_mem)) ->
  WriteSuccessWithdrawalsRecordedRun 15
    (writeSuccess15d10Before regs global, priorLog) segments after ->
  exists prefix output suffix prefixStates outputStates suffixStates,
    segments = (prefix ++ output) ++ suffix /\
    WriteSuccessWithdrawalsPositionEdges prefix prefixStates /\
    WriteSuccessWithdrawalsPositionEdges output outputStates /\
    WriteSuccessWithdrawalsPositionEdges suffix suffixStates /\
    (forall offset stateAt,
      (offset < 7)%nat ->
      nth_error prefixStates offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining (start + offset) stateAt) /\
    (forall offset stateAt,
      (offset < 5)%nat ->
      nth_error outputStates offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining
        (start + (7 + offset))%nat stateAt) /\
    (forall offset stateAt,
      (offset < 3)%nat ->
      nth_error suffixStates offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining
        (start + (12 + offset))%nat stateAt).
Proof.
  intros Hstart Hpc Hx1 Hx2 Hx10 Hx9 Hcounter HreturnAlign HreturnTrace
    HstackAlign HramLower HramUpper Hscratch Hrange Hbacked Hframe Htable Hfacts
    Hmmio Hrecorded.
  destruct (writeSuccessWithdrawalsRecordedRunSplit 7 8
    (writeSuccess15d10Before regs global, priorLog) segments after Hrecorded) as
    (prefix & middle & rest & Hsegments & Hprefix & Hrest).
  destruct (writeSuccessWithdrawalsRecordedRunSplit 5 3 middle rest after
    Hrest) as (output & suffixBefore & suffix & HrestSegments & Houtput & Hsuffix).
  destruct (writeSuccessEncoderIntPrefixRecordedPositionPath regs global value
    sp returnAddress scratch priorLog prefix middle Hpc Hx1 Hx2 Hx10 Hscratch
    Hrange HstackAlign HramLower HramUpper Htable Hfacts Hprefix) as
    (m14 & s14 & m18 & s18 & result14 & result18 & discardedPrefixStates &
     Hmiddle & HprefixSegments & HprefixLength & HprefixStart & HprefixEnd &
     HdiscardedPrefixEdges).
  subst middle.
  destruct (writeSuccessWithdrawalsEncoderIntPrefixActualPositions remaining
    start regs global value sp returnAddress scratch priorLog prefix
    (writeSuccess10190Before (writeSuccessEncoderIntRegs7 regs sp)
      (writeSuccessEncoderIntGlobal2 global sp returnAddress value), priorLog)
    Hstart Hpc Hx1 Hx2 Hx10 Hx9 Hcounter Hscratch Hrange HstackAlign HramLower
    HramUpper Htable Hfacts Hprefix) as (prefixStates & HprefixEdges & HprefixFacts).
  set (global2 := writeSuccessEncoderIntGlobal2 global sp returnAddress value).
  set (regs7 := writeSuccessEncoderIntRegs7 regs sp).
  have Htable2 : writeSuccessWithdrawalsInstructionTable global2.
  { unfold global2, writeSuccessEncoderIntGlobal2,
      writeSuccessEncoderIntGlobal1, writeSuccess15d18Global,
      writeSuccess15d14Global. cbn. exact Htable. }
  have Hfacts7 : writeSuccessWithdrawalsOperationalRegisterFacts regs7.
  { unfold regs7. apply writeSuccessEncoderIntRegs7Facts. exact Hfacts. }
  have Hx9_7 : regs7 !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold regs7. rewrite writeSuccessEncoderIntRegs7LookupOther;
      try discriminate. exact Hx9. }
  have Hmmio2 : set_Forall (fun address =>
      ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
      (dom global2.(seq_mem)).
  { have Hframe2 : writeSuccessMemoryRangeFrame (bv_unsigned sp - 16) 16
        global2.(seq_mem) memoryFrame.
    { unfold global2. apply writeSuccessEncoderIntGlobal2Frame; assumption. }
    destruct Hframe as (Hdom & _). destruct Hframe2 as (Hdom2 & _).
    rewrite Hdom2. rewrite <- Hdom. exact Hmmio. }
  have HreturnCode : global2.(seq_instrs) !! writeSuccess15d28Link = Some a15d2c.
  { have Hcode : global2.(seq_instrs) !! Z_to_bv 64 0x15d2c = Some a15d2c.
    { apply Htable2. unfold writeSuccessWithdrawalsInstructionSource,
        writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
    destruct writeSuccess15d28ValuesExact as (_ & Hlink & _).
    rewrite Hlink. exact Hcode. }
  destruct (writeSuccessOutputRecordedPositionPath regs7 global2
    (sp - BV 64 16)%bv (BV 64 8) writeSuccess15d28Link a15d2c priorLog
    output suffixBefore (writeSuccessEncoderIntRegs7Pc regs sp)
    (writeSuccessEncoderIntRegs7X1 regs sp)
    (writeSuccessEncoderIntRegs7X10 regs sp)
    (writeSuccessEncoderIntRegs7X11 regs sp)
    ltac:(apply bv_eq; native_compute; reflexivity) HreturnCode Htable2 Hfacts7
    Hmmio2 Houtput) as
    (mo & so & result98 & result9c & discardedOutputStates & HoutputSegments &
     HsuffixBefore & HoutputLength & HoutputStart & HoutputEnd &
     HdiscardedOutputEdges).
  subst suffixBefore.
  have HsavedRead : read_mem global2.(seq_mem) (bv_unsigned sp - 8) 8%N =
      Some (bv_to_bvn returnAddress).
  { unfold global2. apply writeSuccessEncoderIntAfterStoresRead. exact Hrange. }
  destruct (writeSuccessWithdrawalsEncoderIntOutputActualPositions remaining
    start regs7 global2 (sp - BV 64 16)%bv (BV 64 8) sp returnAddress a15d2c
    priorLog output
    (writeSuccess101a0After (writeSuccessOutputRegs4 regs7) global2
      writeSuccess15d28Link,
     priorLog ++
       [(SWriteMem (BV 64 0x2401a0c0) (bv_to_bvn (sp - BV 64 16)%bv),
           global2.(seq_mem));
        (SWriteMem (BV 64 0x2401a0c8) (bv_to_bvn (BV 64 8)),
           global2.(seq_mem))])
    Hstart (writeSuccessEncoderIntRegs7Pc regs sp)
    (writeSuccessEncoderIntRegs7X1 regs sp)
    (writeSuccessEncoderIntRegs7X2 regs sp)
    (writeSuccessEncoderIntRegs7X10 regs sp)
    (writeSuccessEncoderIntRegs7X11 regs sp) Hx9_7 Hcounter HsavedRead Hrange
    HreturnCode Htable2 Hfacts7 Hmmio2 Houtput) as
    (outputStates & HoutputEdges & HoutputFacts).
  have HreturnTrace2 : global2.(seq_instrs) !! returnAddress = Some returnTrace.
  { unfold global2, writeSuccessEncoderIntGlobal2,
      writeSuccessEncoderIntGlobal1, writeSuccess15d18Global,
      writeSuccess15d14Global. cbn. exact HreturnTrace. }
  have Hjoin :
      writeSuccess101a0After (writeSuccessOutputRegs4 regs7) global2
        writeSuccess15d28Link =
      writeSuccess15d2cBefore (writeSuccessEncoderIntAfterOutputRegs regs7)
        global2.
  { unfold writeSuccess101a0After, writeSuccess15d2cBefore,
      writeSuccessEncoderIntAfterOutputRegs.
    rewrite (writeSuccessOutputReturnTargetExact writeSuccess15d28Link
      ltac:(apply bv_eq; native_compute; reflexivity)) HreturnCode.
    reflexivity. }
  rewrite Hjoin in Hsuffix.
  destruct (writeSuccessWithdrawalsEncoderIntSuffixActualPositions remaining
    start regs7 global2 sp returnAddress returnTrace
    (priorLog ++
      [(SWriteMem (BV 64 0x2401a0c0) (bv_to_bvn (sp - BV 64 16)%bv),
          global2.(seq_mem));
       (SWriteMem (BV 64 0x2401a0c8) (bv_to_bvn (BV 64 8)),
          global2.(seq_mem))])
    suffix after Hstart (writeSuccessEncoderIntRegs7X2 regs sp)
    (writeSuccessEncoderIntRegs7X1 regs sp) Hx9_7 Hcounter Hfacts7 HsavedRead
    Hrange HstackAlign HramLower HramUpper HreturnAlign HreturnTrace2 Htable2
    Hsuffix) as (suffixStates & HsuffixEdges & HsuffixFacts).
  exists prefix, output, suffix, prefixStates, outputStates, suffixStates.
  rewrite Hsegments HrestSegments. repeat split; try assumption.
  apply app_assoc.
Qed.

Print Assumptions writeSuccessWithdrawalsEncoderIntActualPositions.
