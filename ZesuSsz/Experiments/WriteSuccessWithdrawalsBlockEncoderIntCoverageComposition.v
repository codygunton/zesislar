From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d2c.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessInstructionRunSplit.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntPrefixCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSuffix.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSuffixCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSilent.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntFrame.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d30.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d34.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessEncoderIntRunExact
    (regs : reg_map) (global : seq_global_state)
    (value sp returnAddress : bv 64) scratch memoryFrame returnTrace
    segments after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d10)) ->
  regs !! "x1" = Some (RVal_Bits returnAddress) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some (RVal_Bits value) ->
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
  IslaInstructionRun 15 (writeSuccess15d10Before regs global) segments after ->
  after = writeSuccess15d34After
    (writeSuccess15d30Regs
      (writeSuccess15d2cRegs
        (writeSuccessEncoderIntAfterOutputRegs
          (writeSuccessEncoderIntRegs7 regs sp)) returnAddress)
      (sp - BV 64 16)%bv)
    (writeSuccessEncoderIntGlobal2 global sp returnAddress value)
    returnAddress /\
  segmentRecords (writeSuccess15d10Before regs global)
    (flattenMicroObservations segments) =
    [(SWriteMem (BV 64 0x2401a0c0)
        (bv_to_bvn (sp - BV 64 16)%bv),
      (writeSuccessEncoderIntGlobal2 global sp returnAddress value).(seq_mem));
     (SWriteMem (BV 64 0x2401a0c8) (bv_to_bvn (BV 64 8)),
      (writeSuccessEncoderIntGlobal2 global sp returnAddress value).(seq_mem))].
Proof.
  intros Hpc Hx1 Hx2 Hx10 HreturnAlign HreturnTrace HstackAlign HramLower
    HramUpper Hscratch Hrange Hbacked Hframe Htable Hfacts Hmmio Hrun.
  destruct (islaInstructionRun_split 7 8 _ _ _ Hrun) as
    (prefix & middle & rest & Hsegments & Hprefix & Hrest).
  destruct (islaInstructionRun_split 5 3 _ _ _ Hrest) as
    (output & suffixBefore & suffix & HrestSegments & Houtput & Hsuffix).
  destruct (writeSuccessEncoderIntPrefixRunCovered regs global value sp
    returnAddress scratch prefix middle Hpc Hx1 Hx2 Hx10 Hscratch Hrange
    HstackAlign HramLower HramUpper Htable Hfacts Hprefix) as
    (m14 & s14 & m18 & s18 & result14 & result18 & Hmiddle & HprefixSegments).
  subst middle.
  set (global2 := writeSuccessEncoderIntGlobal2 global sp returnAddress value).
  set (regs7 := writeSuccessEncoderIntRegs7 regs sp).
  have Htable2 : writeSuccessWithdrawalsInstructionTable global2.
  { unfold global2, writeSuccessEncoderIntGlobal2,
      writeSuccessEncoderIntGlobal1, writeSuccess15d18Global,
      writeSuccess15d14Global. cbn. exact Htable. }
  have Hfacts7 : writeSuccessWithdrawalsOperationalRegisterFacts regs7.
  { unfold regs7. apply writeSuccessEncoderIntRegs7Facts. exact Hfacts. }
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
  destruct (writeSuccessOutputRunExact regs7 global2
    (sp - BV 64 16)%bv (BV 64 8) writeSuccess15d28Link a15d2c
    output suffixBefore (writeSuccessEncoderIntRegs7Pc regs sp)
    (writeSuccessEncoderIntRegs7X1 regs sp)
    (writeSuccessEncoderIntRegs7X10 regs sp)
    (writeSuccessEncoderIntRegs7X11 regs sp)
    ltac:(apply bv_eq; native_compute; reflexivity) HreturnCode Htable2 Hfacts7
    Hmmio2 Houtput) as
    (mo & so & result98 & result9c & HoutputSegments & HsuffixBefore &
     HoutputRecords).
  subst suffixBefore.
  have HsavedRead : read_mem global2.(seq_mem) (bv_unsigned sp - 8) 8%N =
      Some (bv_to_bvn returnAddress).
  { unfold global2. apply writeSuccessEncoderIntAfterStoresRead. exact Hrange. }
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
  rewrite Hjoin in Houtput.
  destruct (writeSuccessEncoderIntSuffixRunCovered regs7 global2 sp
    returnAddress suffix after (writeSuccessEncoderIntRegs7X2 regs sp)
    (writeSuccessEncoderIntRegs7X1 regs sp) Hfacts7 HsavedRead Hrange
    HstackAlign HramLower HramUpper HreturnAlign Htable2 Hsuffix) as
    (ms & ss & Hafter & HsuffixSegments).
  split; first exact Hafter.
  rewrite Hsegments HrestSegments flattenMicroObservationsApp.
  rewrite (segmentRecords_app (writeSuccess15d10Before regs global)
    (flattenMicroObservations prefix)
    (writeSuccess10190Before regs7 global2)
    (flattenMicroObservations (output ++ suffix))).
  2:{ exact (islaInstructionRunCorrespondence _ _ _ _ Hprefix). }
  rewrite HprefixSegments writeSuccessEncoderIntPrefixRecordsEmpty.
  rewrite flattenMicroObservationsApp.
  rewrite (segmentRecords_app (writeSuccess10190Before regs7 global2)
    (flattenMicroObservations output)
    (writeSuccess15d2cBefore (writeSuccessEncoderIntAfterOutputRegs regs7)
      global2)
    (flattenMicroObservations suffix)).
  2:{ exact (islaInstructionRunCorrespondence _ _ _ _ Houtput). }
  rewrite HoutputRecords HsuffixSegments.
  rewrite (writeSuccessEncoderIntSuffixRecords regs7 global2 sp returnAddress
    ms ss returnTrace HreturnAlign HreturnTrace2).
  reflexivity.
Qed.

Print Assumptions writeSuccessEncoderIntRunExact.
