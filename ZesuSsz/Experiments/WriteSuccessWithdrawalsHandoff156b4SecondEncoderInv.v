From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import IslaTraces.write_success_07.a15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156bc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntFrame.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntCallerFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntScratch.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpySupport.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessWithdrawalsFirstEncoderScratch (sp : bv 64)
    (withdrawal : WriteSuccessWithdrawalObservation) :=
  bv_to_little_endian 8 8
    (bv_unsigned (writeSuccessWithdrawalsIndexValue withdrawal)) ++
  bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 0x156b4)).

Lemma writeSuccessWithdrawals156b4SecondEncoderInv args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs global :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
    withdrawal = writeSuccess15d10Before regs global ->
  Inv_encoder_int (writeSuccessWithdrawalsValidatorValue withdrawal) sp
    (Z_to_bv 64 0x156c0)
    (writeSuccessWithdrawalsFirstEncoderScratch sp withdrawal)
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).2.(seq_mem)
    (priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
      (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal))
    (writeSuccessWithdrawalsSecondEncoderEntry regs global sp withdrawal,
     priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
       (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)).
Proof.
  intros Hinv Hprefix Hentry.
  have HfirstInv := writeSuccessWithdrawals156a8EncoderIntInv args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    Hinv Hprefix.
  rewrite Hentry in HfirstInv.
  have Htable : writeSuccessWithdrawalsInstructionTable global by
    (unfold Inv_encoder_int in HfirstInv; cbn in HfirstInv; tauto).
  destruct (writeSuccessEncoderIntCaller156b4 global Htable) as
    (HfirstAlign & firstTrace & HfirstCode).
  have HendGlobal := writeSuccessWithdrawalsEncoderIntEndpointGlobal regs global
    sp (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)
    firstTrace HfirstAlign HfirstCode.
  have Hfacts : writeSuccessWithdrawalsOperationalRegisterFacts regs by
    (unfold Inv_encoder_int in HfirstInv; cbn in HfirstInv; tauto).
  have HendFacts := writeSuccessEncoderIntEndpointFacts regs sp
    (Z_to_bv 64 0x156b4) Hfacts.
  have HendExact := writeSuccessEncoderIntEndpointExact regs global sp
    (writeSuccessWithdrawalsIndexValue withdrawal) (Z_to_bv 64 0x156b4)
    firstTrace HfirstAlign
    ltac:(rewrite writeSuccessWithdrawalsEncoderIntGlobal2Instrs; exact HfirstCode).
  have HendRegsEq :
      (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs) =
      writeSuccessEncoderIntEndpointRegs regs sp (Z_to_bv 64 0x156b4).
  { unfold writeSuccessWithdrawalsFirstEncoderEndpoint.
    exact (f_equal (fun machine => machine.1.(seq_regs)) HendExact). }
  have HspEnd := writeSuccessWithdrawalsEncoderIntEndpointX2 regs global sp
    (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)
    firstTrace HfirstAlign HfirstCode.
  have Hrange : islaMemoryRange (bv_unsigned sp - 16) 16 by
    (unfold Inv_encoder_int in HfirstInv; cbn in HfirstInv; tauto).
  have Hbacked : forall location,
      bv_unsigned sp - 16 <= location < bv_unsigned sp ->
      is_Some (global.(seq_mem) !! Z_to_bv 64 location) by
    (unfold Inv_encoder_int in HfirstInv; cbn in HfirstInv; tauto).
  have Hframe0 : writeSuccessMemoryRangeFrame (bv_unsigned sp - 16) 16
      global.(seq_mem) global.(seq_mem) by
    (split; [reflexivity|intros; reflexivity]).
  have HendFrame := writeSuccessEncoderIntGlobal2Frame global global.(seq_mem) sp
    (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)
    Hrange Hbacked Hframe0.
  have Hscratch := writeSuccessEncoderIntAfterStoresScratch global sp
    (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal) Hrange.
  have HtableEnd : writeSuccessWithdrawalsInstructionTable
      (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).2.
  { unfold writeSuccessWithdrawalsFirstEncoderEndpoint. rewrite HendGlobal.
    unfold writeSuccessWithdrawalsInstructionTable in Htable |- *.
    intros pc trace Hsource. apply Htable. exact Hsource. }
  destruct (writeSuccessEncoderIntCaller156c0
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).2
    HtableEnd) as (HreturnAlign & returnTrace & HreturnCode).
  set (endRegs :=
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)).
  set (r1 := writeSuccess156b4Regs endRegs
    (writeSuccessWithdrawalsValidatorValue withdrawal)).
  set (r2 := writeSuccess156b8Regs r1).
  have Hfacts1 : writeSuccessWithdrawalsOperationalRegisterFacts r1.
  { unfold r1, writeSuccess156b4Regs.
    apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|].
    apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|].
    unfold endRegs. rewrite HendRegsEq. exact HendFacts. }
  have Hfacts2 : writeSuccessWithdrawalsOperationalRegisterFacts r2.
  { unfold r2, writeSuccess156b8Regs.
    apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|].
    apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|]. exact Hfacts1. }
  have Hfacts3 : writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccess156bcRegs r2).
  { unfold writeSuccess156bcRegs.
    apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|].
    apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|]. exact Hfacts2. }
  unfold Inv_encoder_int.
  split.
  { split; first reflexivity.
    exists (Z_to_bv 64 0x15d10), a15d10. repeat split.
    - unfold writeSuccessWithdrawalsSecondEncoderEntry, writeSuccess156bcAfter,
        writeSuccess15694Local. cbn. unfold r2, r1, endRegs.
      unfold writeSuccess156bcRegs. rewrite lookup_insert.
      destruct writeSuccess156bcValuesExact as (_ & _ & _ & Htarget).
      rewrite Htarget. reflexivity.
    - apply HtableEnd. cbn. tauto. }
  split; first reflexivity.
  split.
  { unfold writeSuccessWithdrawalsConcretePc,
      writeSuccessWithdrawalsSecondEncoderEntry, writeSuccess156bcAfter,
      writeSuccess15694Local. cbn. unfold writeSuccess156bcRegs.
    rewrite lookup_insert. destruct writeSuccess156bcValuesExact as (_ & _ & _ & Htarget).
    rewrite Htarget. native_compute. reflexivity. }
  split.
  { unfold writeSuccessWithdrawalsSecondEncoderEntry, writeSuccess156bcAfter,
      writeSuccess15694Local. cbn. unfold writeSuccess156bcRegs.
    rewrite lookup_insert_ne; last discriminate. rewrite lookup_insert.
    destruct writeSuccess156bcValuesExact as (_ & Hlink & _). rewrite Hlink.
    reflexivity. }
  split.
  { unfold writeSuccessWithdrawalsSecondEncoderEntry, writeSuccess156bcAfter,
      writeSuccess15694Local. cbn.
    rewrite writeSuccess156bcRegsLookupOther; try discriminate.
    rewrite writeSuccess156b8RegsLookupOther; try discriminate.
    rewrite writeSuccess156b4RegsLookupOther; try discriminate. exact HspEnd. }
  split.
  { unfold writeSuccessWithdrawalsSecondEncoderEntry, writeSuccess156bcAfter,
      writeSuccess15694Local. cbn.
    rewrite writeSuccess156bcRegsLookupOther; try discriminate.
    rewrite writeSuccess156b8RegsLookupOther; try discriminate.
    unfold writeSuccess156b4Regs. rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert. reflexivity. }
  split; first exact HreturnAlign.
  split; first (exists returnTrace; exact HreturnCode).
  split.
  { have Halign16 : bv_unsigned sp `mod` 16 = 0 by
      (unfold Inv_15694 in Hinv; tauto).
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in Halign16; [|lia].
    destruct Halign16 as [factor Hfactor]. exists (2 * factor). lia. }
  split; first (unfold Inv_15694 in Hinv; tauto).
  split.
  { have Hupper : bv_unsigned sp + 1792 < 0x40000000 by
      (unfold Inv_15694 in Hinv; tauto). lia. }
  split.
  { unfold writeSuccessWithdrawalsSecondEncoderEntry, writeSuccess156bcAfter,
      writeSuccess15694Local. cbn. unfold writeSuccessWithdrawalsFirstEncoderScratch.
    unfold writeSuccessWithdrawalsFirstEncoderEndpoint. rewrite HendGlobal.
    exact Hscratch. }
  split; first exact Hrange.
  split.
  { intros location Hlocation. apply writeSuccessReadMemListBacked with
      (address := bv_unsigned sp - 16) (length := 16%nat)
      (bytes := writeSuccessWithdrawalsFirstEncoderScratch sp withdrawal).
    - unfold writeSuccessWithdrawalsSecondEncoderEntry, writeSuccess156bcAfter,
        writeSuccess15694Local. cbn. unfold writeSuccessWithdrawalsFirstEncoderScratch,
        writeSuccessWithdrawalsFirstEncoderEndpoint. rewrite HendGlobal. exact Hscratch.
    - lia. }
  split; first (split; [reflexivity|intros; reflexivity]).
  split; first exact HtableEnd.
  split; first exact Hfacts3.
  split.
  { unfold writeSuccessWithdrawalsSecondEncoderEntry, writeSuccess156bcAfter,
      writeSuccess15694Local. cbn.
    have Hdom := proj1 HendFrame.
    rewrite HendGlobal.
    rewrite Hdom. unfold Inv_encoder_int in HfirstInv. cbn in HfirstInv. tauto. }
  reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawals156b4SecondEncoderInv.
