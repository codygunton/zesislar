From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d10.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntCallerFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntScratch.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalAmountRead.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156d0EncoderIntContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOutputEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpySupport.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessWithdrawalsSecondEncoderScratch (sp : bv 64)
    (withdrawal : WriteSuccessWithdrawalObservation) :=
  bv_to_little_endian 8 8
    (bv_unsigned (writeSuccessWithdrawalsValidatorValue withdrawal)) ++
  bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 0x156c0)).

Lemma writeSuccessWithdrawals156d0FinalEncoderInv args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    outputRegs global outputPriorLog (firstValue secondValue : bv 64) :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  global = writeSuccessEncoderIntGlobal2
    (writeSuccessEncoderIntGlobal2
      (writeSuccessWithdrawals156a8Global regs0 global0 sp pointer current) sp
      (Z_to_bv 64 0x156b4) firstValue) sp
    (Z_to_bv 64 0x156c0) secondValue ->
  secondValue = writeSuccessWithdrawalsValidatorValue withdrawal ->
  outputRegs !! "x2" = Some (RVal_Bits sp) ->
  Inv_write_output (sp + BV 64 1768)%bv (BV 64 20)
    (Z_to_bv 64 0x156d0) (writeSuccessWithdrawalAddressBytes withdrawal)
    outputPriorLog (writeSuccess10190Before outputRegs global, outputPriorLog) ->
  Inv_encoder_int (writeSuccessWithdrawalsAmountValue withdrawal) sp
    (Z_to_bv 64 0x156dc)
    (writeSuccessWithdrawalsSecondEncoderScratch sp withdrawal)
    global.(seq_mem)
    (outputPriorLog ++ writeSuccessWithdrawalsOutputRecordsExact global
      (sp + BV 64 1768)%bv (BV 64 20))
    (writeSuccess156d8After
      (writeSuccess156d4Regs
        (writeSuccess156d0Regs
          (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0))
          (writeSuccessWithdrawalsAmountValue withdrawal))) global,
     outputPriorLog ++ writeSuccessWithdrawalsOutputRecordsExact global
       (sp + BV 64 1768)%bv (BV 64 20)).
Proof.
  intros Hinv Hglobal HsecondValue Hx2 HoutputInv. subst secondValue.
  have Htable : writeSuccessWithdrawalsInstructionTable global by
    (unfold Inv_write_output in HoutputInv; cbn in HoutputInv; tauto).
  have Hfacts0 : writeSuccessWithdrawalsOperationalRegisterFacts outputRegs by
    (unfold Inv_write_output in HoutputInv; cbn in HoutputInv; tauto).
  set (r0 := writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0)).
  set (r1 := writeSuccess156d0Regs r0
    (writeSuccessWithdrawalsAmountValue withdrawal)).
  set (r2 := writeSuccess156d4Regs r1).
  have Hfacts : writeSuccessWithdrawalsOperationalRegisterFacts r0 by
    (unfold r0; apply writeSuccessOutputEndpointFacts; exact Hfacts0).
  have Hsp : r0 !! "x2" = Some (RVal_Bits sp) by
    (unfold r0; apply writeSuccessWithdrawalsOutputEndpointX2; exact Hx2).
  have HspAlign : bv_unsigned sp `mod` 16 = 0 by
    (unfold Inv_15694 in Hinv; tauto).
  have HspLower : 0x20000000 <= bv_unsigned sp - 16 by
    (unfold Inv_15694 in Hinv; tauto).
  have HspUpper : bv_unsigned sp + 1792 < 0x40000000 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hrange : islaMemoryRange (bv_unsigned sp - 16) 16.
  { unfold islaMemoryRange. pose proof (bv_unsigned_in_range 64 sp). lia. }
  have Hscratch : read_mem_list global.(seq_mem) (bv_unsigned sp - 16) 16%N =
      Some (writeSuccessWithdrawalsSecondEncoderScratch sp withdrawal).
  { rewrite Hglobal. unfold writeSuccessWithdrawalsSecondEncoderScratch.
    apply writeSuccessEncoderIntAfterStoresScratch. exact Hrange. }
  have Hbacked : forall location,
      bv_unsigned sp - 16 <= location < bv_unsigned sp ->
      is_Some (global.(seq_mem) !! Z_to_bv 64 location).
  { intros location Hlocation. apply writeSuccessReadMemListBacked with
      (address := bv_unsigned sp - 16) (length := 16%nat)
      (bytes := writeSuccessWithdrawalsSecondEncoderScratch sp withdrawal).
    - exact Hscratch.
    - lia. }
  destruct (writeSuccessEncoderIntCaller156dc global Htable) as
    (HreturnAlign & returnTrace & HreturnCode).
  have Hfacts1 : writeSuccessWithdrawalsOperationalRegisterFacts r1.
  { unfold r1, writeSuccess156d0Regs.
    apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|].
    apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|]. exact Hfacts. }
  have Hfacts2 : writeSuccessWithdrawalsOperationalRegisterFacts r2.
  { unfold r2, writeSuccess156d4Regs.
    apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|].
    apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|]. exact Hfacts1. }
  have Hfacts3 : writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccess156d8Regs r2).
  { unfold writeSuccess156d8Regs.
    apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|].
    apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|]. exact Hfacts2. }
  unfold Inv_encoder_int.
  split.
  { split; first reflexivity.
    exists (Z_to_bv 64 0x15d10), a15d10. repeat split.
    - unfold writeSuccess156d8After, writeSuccess15694Local. cbn.
      unfold writeSuccess156d8Regs. rewrite lookup_insert.
      destruct writeSuccess156d8ValuesExact as (_ & _ & _ & Htarget).
      rewrite Htarget. reflexivity.
    - apply Htable. cbn. tauto. }
  split; first reflexivity.
  split.
  { unfold writeSuccessWithdrawalsConcretePc, writeSuccess156d8After,
      writeSuccess15694Local. cbn. unfold writeSuccess156d8Regs.
    rewrite lookup_insert. destruct writeSuccess156d8ValuesExact as
      (_ & _ & _ & Htarget). rewrite Htarget. reflexivity. }
  split.
  { unfold writeSuccess156d8After, writeSuccess15694Local. cbn.
    unfold writeSuccess156d8Regs. rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert. destruct writeSuccess156d8ValuesExact as
      (_ & Hlink & _). rewrite Hlink. reflexivity. }
  split.
  { unfold writeSuccess156d8After, writeSuccess15694Local. cbn.
    rewrite writeSuccess156d8RegsLookupOther; try discriminate.
    unfold r2. rewrite writeSuccess156d4RegsLookupOther; try discriminate.
    unfold r1. rewrite writeSuccess156d0RegsLookupOther; try discriminate.
    exact Hsp. }
  split.
  { unfold writeSuccess156d8After, writeSuccess15694Local. cbn.
    rewrite writeSuccess156d8RegsLookupOther; try discriminate.
    unfold r2. rewrite writeSuccess156d4RegsLookupOther; try discriminate.
    unfold r1, writeSuccess156d0Regs. rewrite lookup_insert_ne;
      last discriminate. rewrite lookup_insert. reflexivity. }
  split; first exact HreturnAlign.
  split; first (exists returnTrace; exact HreturnCode).
  split.
  { apply Z.mod_divide; [lia|]. apply Z.mod_divide in HspAlign; [|lia].
    destruct HspAlign as [factor Hfactor]. exists (2 * factor). lia. }
  split; first exact HspLower.
  split; first lia.
  split; first exact Hscratch.
  split; first exact Hrange.
  split; first exact Hbacked.
  split; first (split; [reflexivity|intros; reflexivity]).
  split; first exact Htable.
  split; first exact Hfacts3.
  split.
  { unfold Inv_write_output in HoutputInv. cbn in HoutputInv. tauto. }
  reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawals156d0FinalEncoderInv.
