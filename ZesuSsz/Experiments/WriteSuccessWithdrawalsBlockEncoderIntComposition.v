From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d2c.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessBlockFramework.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntPrefix.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntOutput.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSuffix.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntFrame.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessEncoderIntComposedRun
    (regs : reg_map) (global : seq_global_state)
    (value sp returnAddress : bv 64) scratch memoryFrame
    (priorLog : list WriteSuccessWithdrawalsRecord) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d10)) ->
  regs !! "x1" = Some (RVal_Bits returnAddress) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some (RVal_Bits value) ->
  bv_extract 0 2 returnAddress = BV 2 0 ->
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
  exists segments after records,
    IslaInstructionRun 15 (writeSuccess15d10Before regs global) segments after /\
    (match after.1.(seq_regs) !! after.1.(seq_pc_reg) with
     | Some (RVal_Bits pc) => Some (bvn_unsigned pc)
     | _ => None
     end) = Some (bv_unsigned returnAddress) /\
    read_mem_list after.2.(seq_mem) (bv_unsigned sp - 16) 8%N =
      Some (bv_to_little_endian 8 8 (bv_unsigned value)) /\
    writeSuccessMemoryRangeFrame (bv_unsigned sp - 16) 16
      after.2.(seq_mem) memoryFrame /\
    writeSuccessOutputRecords (sp - BV 64 16)%bv (BV 64 8)
      (bv_to_little_endian 8 8 (bv_unsigned value)) records.
Proof.
  intros Hpc Hx1 Hx2 Hx10 HreturnAlign HstackAlign HramLower HramUpper
    Hscratch Hrange Hbacked Hframe Htable Hfacts Hmmio.
  destruct (writeSuccessEncoderIntPrefixRun regs global value sp returnAddress
    scratch Hpc Hx1 Hx2 Hx10 Hscratch Hrange HstackAlign HramLower HramUpper
    Htable Hfacts) as (prefixSegments & Hprefix).
  set (global2 := writeSuccessEncoderIntGlobal2 global sp returnAddress value).
  set (regs7 := writeSuccessEncoderIntRegs7 regs sp).
  have Hframe2 : writeSuccessMemoryRangeFrame (bv_unsigned sp - 16) 16
      global2.(seq_mem) memoryFrame.
  { unfold global2. apply writeSuccessEncoderIntGlobal2Frame; assumption. }
  have Htable2 : writeSuccessWithdrawalsInstructionTable global2.
  { unfold global2, writeSuccessEncoderIntGlobal2,
      writeSuccessEncoderIntGlobal1, writeSuccess15d18Global,
      writeSuccess15d14Global. cbn. exact Htable. }
  have Hfacts7 : writeSuccessWithdrawalsOperationalRegisterFacts regs7.
  { unfold regs7. apply writeSuccessEncoderIntRegs7Facts. exact Hfacts. }
  have Hmmio2 : set_Forall (fun address =>
      ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
      (dom global2.(seq_mem)).
  { destruct Hframe as (Hdom & _). destruct Hframe2 as (Hdom2 & _).
    rewrite Hdom2. rewrite <- Hdom. exact Hmmio. }
  have HreturnCode : global2.(seq_instrs) !! writeSuccess15d28Link =
      Some a15d2c.
  { have Hcode : global2.(seq_instrs) !! Z_to_bv 64 0x15d2c = Some a15d2c.
    { apply Htable2. unfold writeSuccessWithdrawalsInstructionSource,
        writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
    destruct writeSuccess15d28ValuesExact as (_ & Hlink & _).
    rewrite Hlink. exact Hcode. }
  have HdataRead : read_mem_list global2.(seq_mem)
      (bv_unsigned (sp - BV 64 16)%bv) 8%N =
      Some (bv_to_little_endian 8 8 (bv_unsigned value)).
  { rewrite writeSuccessEncoderIntStackUnsigned; [|exact Hrange].
    unfold global2. apply writeSuccessEncoderIntAfterStoresValue. exact Hrange. }
  have Hsize : bv_unsigned (BV 64 8) = Z.of_nat
      (length (bv_to_little_endian 8 8 (bv_unsigned value))).
  { rewrite length_bv_to_little_endian; [native_compute; reflexivity|lia]. }
  have HlinkAlign : bv_extract 0 2 writeSuccess15d28Link = BV 2 0.
  { apply bv_eq. native_compute. reflexivity. }
  destruct (writeSuccessEncoderIntOutputExactRun regs7 global2
    (sp - BV 64 16)%bv (BV 64 8) writeSuccess15d28Link
    (bv_to_little_endian 8 8 (bv_unsigned value)) priorLog a15d2c
    (writeSuccessEncoderIntRegs7Pc regs sp)
    (writeSuccessEncoderIntRegs7X1 regs sp)
    (writeSuccessEncoderIntRegs7X10 regs sp)
    (writeSuccessEncoderIntRegs7X11 regs sp)
    HlinkAlign HreturnCode Hsize HdataRead Htable2
    Hfacts7 Hmmio2) as (outputSegments & records & Houtput & Hrecords).
  have HsavedRead : read_mem global2.(seq_mem) (bv_unsigned sp - 8) 8%N =
      Some (bv_to_bvn returnAddress).
  { unfold global2. apply writeSuccessEncoderIntAfterStoresRead. exact Hrange. }
  destruct (writeSuccessEncoderIntSuffixRun regs7 global2 sp returnAddress
    (writeSuccessEncoderIntRegs7X2 regs sp)
    (writeSuccessEncoderIntRegs7X1 regs sp) Hfacts7 HsavedRead Hrange
    HstackAlign HramLower HramUpper HreturnAlign Htable2) as
    (suffixSegments & after & Hsuffix & HfinalPc & HfinalMemory).
  have Hfirst : IslaInstructionRun 12 (writeSuccess15d10Before regs global)
      (prefixSegments ++ outputSegments)
      (writeSuccess101a0After (writeSuccessOutputRegs4 regs7) global2
        writeSuccess15d28Link).
  { replace 12%nat with (7 + 5)%nat by lia.
    eapply islaInstructionRun_app; eassumption. }
  have Hjoin :
      writeSuccess101a0After (writeSuccessOutputRegs4 regs7) global2
        writeSuccess15d28Link =
      writeSuccess15d2cBefore (writeSuccessEncoderIntAfterOutputRegs regs7)
        global2.
  { unfold writeSuccess101a0After, writeSuccess15d2cBefore,
      writeSuccessEncoderIntAfterOutputRegs.
    rewrite (writeSuccessOutputReturnTargetExact writeSuccess15d28Link
      HlinkAlign) HreturnCode. reflexivity. }
  have Hall : IslaInstructionRun 15 (writeSuccess15d10Before regs global)
      ((prefixSegments ++ outputSegments) ++ suffixSegments) after.
  { replace 15%nat with (12 + 3)%nat by lia.
    rewrite Hjoin in Hfirst.
    eapply islaInstructionRun_app; [exact Hfirst|].
    exact Hsuffix. }
  exists ((prefixSegments ++ outputSegments) ++ suffixSegments), after, records.
  split; first exact Hall. split; first exact HfinalPc.
  split.
  - rewrite HfinalMemory. unfold global2.
    apply writeSuccessEncoderIntAfterStoresValue. exact Hrange.
  - split.
    + rewrite HfinalMemory. exact Hframe2.
    + exact Hrecords.
Qed.

Print Assumptions writeSuccessEncoderIntComposedRun.
