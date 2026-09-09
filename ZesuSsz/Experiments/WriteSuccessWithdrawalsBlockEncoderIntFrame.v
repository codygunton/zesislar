From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessEncoderIntGlobal2Frame global frame
    (sp returnAddress value : bv 64) :
  islaMemoryRange (bv_unsigned sp - 16) 16 ->
  (forall location,
    bv_unsigned sp - 16 <= location < bv_unsigned sp ->
    is_Some (global.(seq_mem) !! Z_to_bv 64 location)) ->
  writeSuccessMemoryRangeFrame (bv_unsigned sp - 16) 16
    global.(seq_mem) frame ->
  writeSuccessMemoryRangeFrame (bv_unsigned sp - 16) 16
    (writeSuccessEncoderIntGlobal2 global sp returnAddress value).(seq_mem)
    frame.
Proof.
  intros Hrange Hbacked (Hdom & Hframe).
  have HreturnLength : length
      (bv_to_little_endian 8 8 (bv_unsigned returnAddress)) = 8%nat.
  { rewrite length_bv_to_little_endian; lia. }
  have HvalueLength : length
      (bv_to_little_endian 8 8 (bv_unsigned value)) = 8%nat.
  { rewrite length_bv_to_little_endian; lia. }
  have HreturnRange : islaMemoryRange (bv_unsigned sp - 8) 8.
  { unfold islaMemoryRange in Hrange. unfold islaMemoryRange. lia. }
  have HvalueRange : islaMemoryRange (bv_unsigned sp - 16) 8.
  { unfold islaMemoryRange in Hrange. unfold islaMemoryRange. lia. }
  have HreturnBacked : forall location,
      bv_unsigned sp - 8 <= location < bv_unsigned sp ->
      is_Some (global.(seq_mem) !! Z_to_bv 64 location).
  { intros location Hlocation. apply Hbacked. lia. }
  have Hdom1 : dom (write_mem_list global.(seq_mem)
      (Z_to_bv 64 (bv_unsigned sp - 8))
      (bv_to_little_endian 8 8 (bv_unsigned returnAddress))) =
      dom global.(seq_mem).
  { apply write_mem_list_dom; [rewrite HreturnLength; exact HreturnRange|].
    rewrite HreturnLength. intros location Hlocation. apply HreturnBacked. lia. }
  have HvalueBacked : forall location,
      bv_unsigned sp - 16 <= location < bv_unsigned sp - 8 ->
      is_Some ((write_mem_list global.(seq_mem)
        (Z_to_bv 64 (bv_unsigned sp - 8))
        (bv_to_little_endian 8 8 (bv_unsigned returnAddress))) !!
        Z_to_bv 64 location).
  { intros location Hlocation. apply elem_of_dom.
    rewrite Hdom1. apply elem_of_dom. apply Hbacked. lia. }
  rewrite writeSuccessEncoderIntGlobal2Memory. split.
  - rewrite write_mem_list_dom; [rewrite Hdom1 Hdom; reflexivity| |].
    + rewrite HvalueLength. exact HvalueRange.
    + rewrite HvalueLength. intros location Hlocation. apply HvalueBacked. lia.
  - intros address Houtside.
    have HkeyRange := bv_unsigned_in_range 64 address.
    have HkeyPower : (0 <= bv_unsigned address < 2 ^ 64)%Z.
    { unfold bv_modulus in HkeyRange. exact HkeyRange. }
    have HoutsideValue :
        bv_unsigned address < bv_unsigned sp - 16 \/
        bv_unsigned sp - 8 <= bv_unsigned address by lia.
    have HoutsideReturn :
        bv_unsigned address < bv_unsigned sp - 8 \/
        bv_unsigned sp <= bv_unsigned address by lia.
    have HskipValue := write_mem_list_lookup_outside
      (write_mem_list global.(seq_mem) (Z_to_bv 64 (bv_unsigned sp - 8))
        (bv_to_little_endian 8 8 (bv_unsigned returnAddress)))
      (bv_unsigned sp - 16)
      (bv_to_little_endian 8 8 (bv_unsigned value))
      (bv_unsigned address).
    rewrite HvalueLength in HskipValue.
    specialize (HskipValue HvalueRange HkeyPower ltac:(lia)).
    rewrite Z_to_bv_bv_unsigned in HskipValue. rewrite HskipValue.
    have HskipReturn := write_mem_list_lookup_outside global.(seq_mem)
      (bv_unsigned sp - 8)
      (bv_to_little_endian 8 8 (bv_unsigned returnAddress))
      (bv_unsigned address).
    rewrite HreturnLength in HskipReturn.
    specialize (HskipReturn HreturnRange HkeyPower ltac:(lia)).
    rewrite Z_to_bv_bv_unsigned in HskipReturn. rewrite HskipReturn.
    apply Hframe. exact Houtside.
Qed.

Print Assumptions writeSuccessEncoderIntGlobal2Frame.
