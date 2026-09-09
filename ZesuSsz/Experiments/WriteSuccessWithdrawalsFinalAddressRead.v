From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationOff.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpyState.

Open Scope Z_scope.

Lemma writeSuccessWithdrawals156a8AddressRead args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs global :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  read_mem_list
    (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_mem)
    (bv_unsigned (sp + BV 64 1768)%bv) 20 =
    Some (writeSuccessWithdrawalAddressBytes withdrawal).
Proof.
  intros Hinv.
  have Hread := writeSuccessWithdrawals156a8DestinationRead args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs global
    Hinv.
  destruct (read_mem_list_split _ _ 24 24 current Hread) as
    (first & tail & Hsplit & HfirstLength & HtailLength & Hfirst & Htail).
  destruct (read_mem_list_split _ _ 20 4 tail Htail) as
    (addressBytes & padding & HtailSplit & HaddressLength & HpaddingLength &
     Haddress & Hpadding).
  destruct (Inv_15694_current_shape args sp pointer base total processed
    remaining withdrawal allBytes prefix current suffix scratch encoderScratch
    registerFrame memoryFrame priorLog state Hinv) as
    (expectedPadding & HexpectedPaddingLength & HcurrentShape).
  have HtailShape : tail =
      writeSuccessWithdrawalAddressBytes withdrawal ++ expectedPadding.
  { set (header :=
      writeSuccessWithdrawalIntegerBytes
        (observationWithdrawalIndex withdrawal) ++
      writeSuccessWithdrawalIntegerBytes
        (observationWithdrawalValidatorIndex withdrawal) ++
      writeSuccessWithdrawalIntegerBytes
        (observationWithdrawalAmount withdrawal)).
    have HheaderLength : length header = 24%nat.
    { unfold header. rewrite !app_length.
      rewrite !writeSuccessWithdrawalIntegerBytesLength. cbn. lia. }
    have Hcurrent : current = header ++
        (writeSuccessWithdrawalAddressBytes withdrawal ++ expectedPadding).
    { rewrite HcurrentShape. unfold writeSuccessWithdrawalRawBytes, header.
      repeat rewrite app_assoc. reflexivity. }
    pose proof (f_equal (skipn 24) Hsplit) as Hleft.
    rewrite skipn_app HfirstLength Nat.sub_diag skipn_O in Hleft.
    have HdropFirst : skipn 24 first = [] by (apply skipn_all2; lia).
    rewrite HdropFirst in Hleft. cbn in Hleft.
    pose proof (f_equal (skipn 24) Hcurrent) as Hright.
    rewrite skipn_app HheaderLength Nat.sub_diag skipn_O in Hright.
    have HdropHeader : skipn 24 header = [] by (apply skipn_all2; lia).
    rewrite HdropHeader in Hright. cbn in Hright.
    rewrite Hleft in Hright. exact Hright. }
  have HaddressBytes : addressBytes =
      writeSuccessWithdrawalAddressBytes withdrawal.
  { rewrite HtailShape in HtailSplit.
    have Hrepresentation : writeSuccessConcreteRepresentationOff
        (successStackPointer WriteSuccessObservation args)
        (successDecoded WriteSuccessObservation args) state.1.2.(seq_mem)
        (successDecodedAddress WriteSuccessObservation args) by
      (unfold Inv_15694 in Hinv; tauto).
    have Hnth : nth_error (observationWithdrawals
        (successDecoded WriteSuccessObservation args)) processed =
        Some withdrawal by (unfold Inv_15694 in Hinv; tauto).
    have Hvalid := proj1 (writeSuccessRepresentationWithdrawalAt _ _ _ _ _ _
      Hrepresentation Hnth).
    have HexpectedLength := writeSuccessWithdrawalAddressBytesLength withdrawal
      Hvalid.
    pose proof (f_equal (firstn 20) HtailSplit) as H.
    rewrite firstn_app HexpectedLength Nat.sub_diag firstn_O app_nil_r in H.
    rewrite firstn_app HaddressLength Nat.sub_diag firstn_O app_nil_r in H.
    rewrite firstn_all2 in H; last lia.
    rewrite firstn_all2 in H; last lia. symmetry. exact H. }
  rewrite HaddressBytes in Haddress.
  have Hbase : bv_unsigned (sp + BV 64 1744)%bv = bv_unsigned sp + 1744.
  { have Hupper : bv_unsigned sp + 1792 < 0x40000000 by
      (unfold Inv_15694 in Hinv; tauto).
    apply writeSuccessWithdrawalsPrefixDestinationUnsigned. exact Hupper. }
  have HaddressEq : bv_unsigned (sp + BV 64 1768)%bv =
      bv_unsigned (sp + BV 64 1744)%bv + 24.
  { rewrite Hbase. have Hupper : bv_unsigned sp + 1792 < 0x40000000 by
      (unfold Inv_15694 in Hinv; tauto). bv_solve. }
  rewrite HaddressEq. exact Haddress.
Qed.

Lemma writeSuccessEncoderIntGlobal2ReadListDisjoint global sp returnAddress value
    address count bytes :
  islaMemoryRange (bv_unsigned sp - 16) 16 ->
  islaMemoryRangesDisjoint (bv_unsigned sp - 16) 16 address count ->
  read_mem_list global.(seq_mem) address (N.of_nat count) = Some bytes ->
  read_mem_list
    (writeSuccessEncoderIntGlobal2 global sp returnAddress value).(seq_mem)
    address (N.of_nat count) = Some bytes.
Proof.
  intros Hrange Hdisjoint Hread. rewrite writeSuccessEncoderIntGlobal2Memory.
  have Hlength : length (bv_to_little_endian 8 8 (bv_unsigned value)) = 8%nat by
    (rewrite length_bv_to_little_endian; lia).
  have HreturnLength : length (bv_to_little_endian 8 8
      (bv_unsigned returnAddress)) = 8%nat by
    (rewrite length_bv_to_little_endian; lia).
  rewrite (read_mem_list_write_mem_list_disjoint_eq _ _ _ _ count).
  2: { rewrite Hlength. unfold islaMemoryRange in *. lia. }
  2: { rewrite Hlength. unfold islaMemoryRangesDisjoint in *. lia. }
  rewrite (read_mem_list_write_mem_list_disjoint_eq _ _ _ _ count).
  2: { rewrite HreturnLength. unfold islaMemoryRange in *. lia. }
  2: { rewrite HreturnLength. unfold islaMemoryRangesDisjoint in *. lia. }
  exact Hread.
Qed.

Lemma writeSuccessWithdrawalsFinalAddressRead args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs global
    (firstValue secondValue : bv 64) :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  let firstGlobal := writeSuccessEncoderIntGlobal2
    (writeSuccessWithdrawals156a8Global regs global sp pointer current) sp
    (Z_to_bv 64 0x156b4) firstValue in
  let secondGlobal := writeSuccessEncoderIntGlobal2 firstGlobal sp
    (Z_to_bv 64 0x156c0) secondValue in
  read_mem_list secondGlobal.(seq_mem) (bv_unsigned (sp + BV 64 1768)%bv) 20 =
    Some (writeSuccessWithdrawalAddressBytes withdrawal).
Proof.
  intros Hinv. cbn -[writeSuccessEncoderIntGlobal2].
  have Hinitial := writeSuccessWithdrawals156a8AddressRead args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs global Hinv.
  have HspLower : 0x20000000 <= bv_unsigned sp - 16 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hrange : islaMemoryRange (bv_unsigned sp - 16) 16.
  { unfold islaMemoryRange. pose proof (bv_unsigned_in_range 64 sp).
    unfold bv_modulus in *. cbn in *. lia. }
  have Haddress : bv_unsigned (sp + BV 64 1768)%bv = bv_unsigned sp + 1768.
  { have Hupper : bv_unsigned sp + 1792 < 0x40000000 by
      (unfold Inv_15694 in Hinv; tauto). bv_solve. }
  have Hdisjoint : islaMemoryRangesDisjoint (bv_unsigned sp - 16) 16
      (bv_unsigned (sp + BV 64 1768)%bv) 20.
  { unfold islaMemoryRangesDisjoint. rewrite Haddress. lia. }
  apply (writeSuccessEncoderIntGlobal2ReadListDisjoint
    (writeSuccessEncoderIntGlobal2
      (writeSuccessWithdrawals156a8Global regs global sp pointer current) sp
      (Z_to_bv 64 0x156b4) firstValue) sp (Z_to_bv 64 0x156c0) secondValue
    (bv_unsigned (sp + BV 64 1768)%bv) 20
    (writeSuccessWithdrawalAddressBytes withdrawal) Hrange Hdisjoint).
  apply (writeSuccessEncoderIntGlobal2ReadListDisjoint
    (writeSuccessWithdrawals156a8Global regs global sp pointer current) sp
    (Z_to_bv 64 0x156b4) firstValue
    (bv_unsigned (sp + BV 64 1768)%bv) 20
    (writeSuccessWithdrawalAddressBytes withdrawal) Hrange Hdisjoint Hinitial).
Qed.

Print Assumptions writeSuccessWithdrawals156a8AddressRead.
Print Assumptions writeSuccessEncoderIntGlobal2ReadListDisjoint.
Print Assumptions writeSuccessWithdrawalsFinalAddressRead.
