From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationOff.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessReadMemListMiddle memory base
    (prefix current suffix : list (bv 8)) :
  read_mem_list memory base
      (N.of_nat (length (prefix ++ current ++ suffix))) =
    Some (prefix ++ current ++ suffix) ->
  read_mem_list memory (base + Z.of_nat (length prefix))
      (N.of_nat (length current)) = Some current.
Proof.
  intros Hread.
  rewrite !app_length in Hread.
  destruct (read_mem_list_split memory base (length prefix)
      (length current + length suffix) (prefix ++ current ++ suffix) Hread) as
    (actualPrefix & rest & Hparts & HprefixLength & HrestLength &
      HprefixRead & HrestRead).
  have HactualPrefix : actualPrefix = prefix.
  { have Hfirst := f_equal (firstn (length prefix)) Hparts.
    have Hleft : firstn (length prefix) (prefix ++ current ++ suffix) = prefix.
    { rewrite firstn_app. rewrite firstn_all Nat.sub_diag. cbn.
      rewrite firstn_O app_nil_r. reflexivity. }
    have Hright : firstn (length prefix) (actualPrefix ++ rest) = actualPrefix.
    { rewrite firstn_app. rewrite <- HprefixLength, firstn_all, Nat.sub_diag.
      rewrite firstn_O app_nil_r. reflexivity. }
    rewrite Hleft Hright in Hfirst. symmetry. exact Hfirst. }
  have Hrest : rest = current ++ suffix.
  { subst actualPrefix.
    apply app_inv_head in Hparts. symmetry. exact Hparts. }
  subst actualPrefix rest.
  destruct (read_mem_list_split memory (base + Z.of_nat (length prefix))
      (length current) (length suffix) (current ++ suffix) HrestRead) as
    (actualCurrent & actualSuffix & HcurrentParts & HcurrentLength &
      HactualSuffixLength & HcurrentRead & HactualSuffixRead).
  have HactualCurrent : actualCurrent = current.
  { have Hfirst := f_equal (firstn (length current)) HcurrentParts.
    have Hleft : firstn (length current) (current ++ suffix) = current.
    { rewrite firstn_app firstn_all Nat.sub_diag. cbn.
      rewrite firstn_O app_nil_r. reflexivity. }
    have Hright : firstn (length current)
        (actualCurrent ++ actualSuffix) = actualCurrent.
    { rewrite firstn_app. rewrite <- HcurrentLength, firstn_all, Nat.sub_diag.
      rewrite firstn_O app_nil_r. reflexivity. }
    rewrite Hleft Hright in Hfirst. symmetry. exact Hfirst. }
  subst actualCurrent. exact HcurrentRead.
Qed.

Lemma writeSuccessWithdrawalsNonfinalSemanticTransition args sp pointer base
    total processed r withdrawal nextWithdrawal allBytes prefix current
    nextCurrent nextSuffix scratch encoderScratch registerFrame memoryFrame
    priorLog state :
  Inv_15694 args sp pointer base total processed (S (S r)) withdrawal
    allBytes prefix current (nextCurrent ++ nextSuffix) scratch encoderScratch
    registerFrame memoryFrame priorLog state ->
  nth_error (observationWithdrawals
    (successDecoded WriteSuccessObservation args)) (S processed) =
    Some nextWithdrawal ->
  length nextCurrent = 48%nat ->
  exists padding nextPadding,
    length padding = 4%nat /\
    current = writeSuccessWithdrawalRawBytes withdrawal padding /\
    bv_unsigned (pointer + BV 64 48)%bv =
      base + 48 * Z.of_nat (S processed) /\
    allBytes = (prefix ++ current) ++ nextCurrent ++ nextSuffix /\
    length (prefix ++ current) = (48 * S processed)%nat /\
    skipn 48 (nextCurrent ++ nextSuffix) = nextSuffix /\
    length nextSuffix = (48 * r)%nat /\
    length nextPadding = 4%nat /\
    nextCurrent = writeSuccessWithdrawalRawBytes nextWithdrawal nextPadding /\
    read_mem_list state.1.2.(seq_mem)
      (bv_unsigned (pointer + BV 64 48)%bv) 48%N = Some nextCurrent /\
    writeSuccessWithdrawalMemory state.1.2.(seq_mem)
      (bv_unsigned (pointer + BV 64 48)%bv) nextWithdrawal.
Proof.
  intros Hinv Hnext HnextLength.
  destruct (Inv_15694_current_shape args sp pointer base total processed
    (S (S r)) withdrawal allBytes prefix current (nextCurrent ++ nextSuffix)
    scratch encoderScratch registerFrame memoryFrame priorLog state Hinv) as
    (padding & HpaddingLength & HcurrentShape).
  have Hall0 : allBytes = prefix ++ current ++ (nextCurrent ++ nextSuffix) by
    (unfold Inv_15694 in Hinv; tauto).
  have Hall : allBytes = (prefix ++ current) ++ nextCurrent ++ nextSuffix.
  { etrans; first exact Hall0. apply app_assoc. }
  have HprefixLength : length prefix = (48 * processed)%nat by
    (unfold Inv_15694 in Hinv; tauto).
  have HcurrentLength : length current = 48%nat by
    (unfold Inv_15694 in Hinv; tauto).
  have HnextSuffixLength : length nextSuffix = (48 * r)%nat.
  { have HsuffixLength : length (nextCurrent ++ nextSuffix) =
        (48 * Nat.pred (S (S r)))%nat by
      (unfold Inv_15694 in Hinv; tauto).
    rewrite app_length HnextLength in HsuffixLength. cbn in HsuffixLength. lia. }
  have Hpointer : bv_unsigned pointer = base + 48 * Z.of_nat processed by
    (unfold Inv_15694 in Hinv; tauto).
  have HbaseUpper : base + Z.of_nat (length allBytes) < 0x40000000 by
    (unfold Inv_15694 in Hinv; tauto).
  have HpointerRange : bv_unsigned pointer + 48 < 2 ^ 64.
  { rewrite Hpointer.
    have HallLength : length allBytes =
        (length prefix + length current + length nextCurrent +
          length nextSuffix)%nat by
      (rewrite Hall; repeat rewrite app_length; lia).
    rewrite HprefixLength HcurrentLength HnextLength in HallLength.
    have HallLengthZ := f_equal Z.of_nat HallLength.
    rewrite !Nat2Z.inj_add in HallLengthZ. cbn in HallLengthZ.
    lia. }
  have HpointerNext := writeSuccessWithdrawalsPointerAdvanceOperational
    pointer base processed Hpointer HpointerRange.
  have HallRead : read_mem_list state.1.2.(seq_mem) base
      (N.of_nat (length allBytes)) = Some allBytes by
    (unfold Inv_15694 in Hinv; tauto).
  have HnextRead : read_mem_list state.1.2.(seq_mem)
      (base + Z.of_nat (length (prefix ++ current)))
      (N.of_nat (length nextCurrent)) = Some nextCurrent.
  { apply (writeSuccessReadMemListMiddle state.1.2.(seq_mem) base
      (prefix ++ current) nextCurrent nextSuffix).
    rewrite <- Hall. exact HallRead. }
  have HnextRead' : read_mem_list state.1.2.(seq_mem)
      (bv_unsigned (pointer + BV 64 48)%bv) 48%N = Some nextCurrent.
  { rewrite HpointerNext.
    replace (base + 48 * Z.of_nat (S processed)) with
      (base + Z.of_nat (length (prefix ++ current))).
    - replace 48%N with (N.of_nat (length nextCurrent)) by
        (rewrite HnextLength; reflexivity).
      exact HnextRead.
    - rewrite app_length HprefixLength HcurrentLength.
      rewrite Nat2Z.inj_add Nat2Z.inj_mul Nat2Z.inj_succ. cbn. lia. }
  have Hitems : writeSuccessWithdrawalItemsAt state.1.2.(seq_mem) base
      (observationWithdrawals (successDecoded WriteSuccessObservation args)) by
    (unfold Inv_15694 in Hinv; tauto).
  have HnextMemory : writeSuccessWithdrawalMemory state.1.2.(seq_mem)
      (bv_unsigned (pointer + BV 64 48)%bv) nextWithdrawal.
  { rewrite HpointerNext. unfold writeSuccessWithdrawalItemsAt in Hitems.
    exact (Hitems (S processed) nextWithdrawal Hnext). }
  have Hrepresentation : writeSuccessConcreteRepresentationOff
      (successStackPointer WriteSuccessObservation args)
      (successDecoded WriteSuccessObservation args) state.1.2.(seq_mem)
      (successDecodedAddress WriteSuccessObservation args) by
    (unfold Inv_15694 in Hinv; tauto).
  have HnextValid := proj1 (writeSuccessRepresentationWithdrawalAt _ _ _ _ _ _
    Hrepresentation Hnext).
  destruct (writeSuccessWithdrawalRawBytesFromMemory _ _ _ _ HnextValid
    HnextMemory HnextRead') as
    (nextPadding & HnextPaddingLength & HnextShape).
  exists padding, nextPadding.
  split; first exact HpaddingLength.
  split; first exact HcurrentShape.
  split; first exact HpointerNext.
  split; first exact Hall.
  split.
  - rewrite app_length HprefixLength HcurrentLength. lia.
  - split.
    + apply writeSuccessWithdrawalsSuffixAdvance. exact HnextLength.
    + split; first exact HnextSuffixLength.
      split; first exact HnextPaddingLength.
      split; first exact HnextShape.
      split; [exact HnextRead' | exact HnextMemory].
Qed.

Lemma writeSuccessWithdrawalsLastSemanticTransition args sp pointer base total
    processed withdrawal allBytes prefix current scratch encoderScratch
    registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed 1 withdrawal allBytes prefix
    current [] scratch encoderScratch registerFrame memoryFrame priorLog state ->
  exists padding,
    length padding = 4%nat /\
    current = writeSuccessWithdrawalRawBytes withdrawal padding /\
    allBytes = prefix ++ current /\
    length (prefix ++ current) = (48 * total)%nat /\
    bv_unsigned (pointer + BV 64 48)%bv =
      base + 48 * Z.of_nat total.
Proof.
  intros Hinv.
  destruct (Inv_15694_current_shape args sp pointer base total processed 1
    withdrawal allBytes prefix current [] scratch encoderScratch registerFrame
    memoryFrame priorLog state Hinv) as
    (padding & HpaddingLength & HcurrentShape).
  have Hall : allBytes = prefix ++ current by
    (unfold Inv_15694 in Hinv; cbn in Hinv; rewrite app_nil_r in Hinv; tauto).
  have HprefixLength : length prefix = (48 * processed)%nat by
    (unfold Inv_15694 in Hinv; tauto).
  have HcurrentLength : length current = 48%nat by
    (unfold Inv_15694 in Hinv; tauto).
  have Htotal : total = (processed + 1)%nat by
    (unfold Inv_15694 in Hinv; tauto).
  have Hpointer : bv_unsigned pointer = base + 48 * Z.of_nat processed by
    (unfold Inv_15694 in Hinv; tauto).
  have HbaseUpper : base + Z.of_nat (length allBytes) < 0x40000000 by
    (unfold Inv_15694 in Hinv; tauto).
  have HpointerRange : bv_unsigned pointer + 48 < 2 ^ 64.
  { rewrite Hpointer.
    rewrite Hall app_length HprefixLength HcurrentLength in HbaseUpper.
    rewrite Nat2Z.inj_add in HbaseUpper. cbn in HbaseUpper. lia. }
  have Hadvance := writeSuccessWithdrawalsPointerAdvanceOperational pointer base
    processed Hpointer HpointerRange.
  exists padding.
  split; first exact HpaddingLength.
  split; first exact HcurrentShape.
  split; first exact Hall.
  split.
  - rewrite app_length HprefixLength HcurrentLength Htotal. lia.
  - rewrite Hadvance Htotal Nat2Z.inj_add. cbn. lia.
Qed.

Print Assumptions writeSuccessReadMemListMiddle.
Print Assumptions writeSuccessWithdrawalsNonfinalSemanticTransition.
Print Assumptions writeSuccessWithdrawalsLastSemanticTransition.
