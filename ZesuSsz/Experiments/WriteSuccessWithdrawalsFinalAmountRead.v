From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpyState.

Open Scope Z_scope.

Definition writeSuccessWithdrawalsAmountValue
    (withdrawal : WriteSuccessWithdrawalObservation) : bv 64 :=
  Z_to_bv 64 (little_endian_to_bv 8
    (writeSuccessWithdrawalIntegerBytes
      (observationWithdrawalAmount withdrawal))).

Lemma writeSuccessWithdrawals156a8AmountRead args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs global :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  read_mem
    (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_mem)
    (bv_unsigned (writeSuccess156d0Address sp)) 8 =
    Some (bv_to_bvn (writeSuccessWithdrawalsAmountValue withdrawal)).
Proof.
  intros Hinv.
  have Hread := writeSuccessWithdrawals156a8DestinationRead args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs global
    Hinv.
  destruct (read_mem_list_split _ _ 8 40 current Hread) as
    (indexBytes & rest & Hsplit & HindexLength & HrestLength & Hindex & Hrest).
  destruct (read_mem_list_split _ _ 8 32 rest Hrest) as
    (validatorBytes & afterValidator & HrestSplit & HvalidatorLength &
     HafterValidatorLength & Hvalidator & HafterValidator).
  destruct (read_mem_list_split _ _ 8 24 afterValidator HafterValidator) as
    (amountBytes & tail & HamountSplit & HamountLength & HtailLength & Hamount &
     Htail).
  destruct (Inv_15694_current_shape args sp pointer base total processed
    remaining withdrawal allBytes prefix current suffix scratch encoderScratch
    registerFrame memoryFrame priorLog state Hinv) as
    (padding & HpaddingLength & HcurrentShape).
  change (current =
    writeSuccessWithdrawalIntegerBytes
      (observationWithdrawalIndex withdrawal) ++
    (writeSuccessWithdrawalIntegerBytes
      (observationWithdrawalValidatorIndex withdrawal) ++
     writeSuccessWithdrawalIntegerBytes
      (observationWithdrawalAmount withdrawal) ++
     writeSuccessWithdrawalAddressBytes withdrawal ++ padding)) in HcurrentShape.
  have HindexBytes : indexBytes = writeSuccessWithdrawalIntegerBytes
      (observationWithdrawalIndex withdrawal).
  { pose proof (f_equal (firstn 8) Hsplit) as H.
    rewrite HcurrentShape in H.
    rewrite firstn_app writeSuccessWithdrawalIntegerBytesLength in H.
    rewrite firstn_all2 in H.
    2: { rewrite writeSuccessWithdrawalIntegerBytesLength. lia. }
    rewrite Nat.sub_diag firstn_O app_nil_r in H.
    rewrite firstn_app HindexLength in H.
    rewrite firstn_all2 in H; last lia.
    rewrite Nat.sub_diag firstn_O app_nil_r in H. symmetry. exact H. }
  have HrestShape : rest =
      writeSuccessWithdrawalIntegerBytes
        (observationWithdrawalValidatorIndex withdrawal) ++
      writeSuccessWithdrawalIntegerBytes
        (observationWithdrawalAmount withdrawal) ++
      writeSuccessWithdrawalAddressBytes withdrawal ++ padding.
  { rewrite HcurrentShape in Hsplit. rewrite HindexBytes in Hsplit.
    apply app_inv_head in Hsplit. symmetry. exact Hsplit. }
  have HvalidatorBytes : validatorBytes = writeSuccessWithdrawalIntegerBytes
      (observationWithdrawalValidatorIndex withdrawal).
  { pose proof (f_equal (firstn 8) HrestSplit) as H.
    rewrite HrestShape in H.
    rewrite firstn_app writeSuccessWithdrawalIntegerBytesLength in H.
    rewrite firstn_all2 in H.
    2: { rewrite writeSuccessWithdrawalIntegerBytesLength. lia. }
    rewrite Nat.sub_diag firstn_O app_nil_r in H.
    rewrite firstn_app HvalidatorLength in H.
    rewrite firstn_all2 in H; last lia.
    rewrite Nat.sub_diag firstn_O app_nil_r in H. symmetry. exact H. }
  have HafterValidatorShape : afterValidator =
      writeSuccessWithdrawalIntegerBytes
        (observationWithdrawalAmount withdrawal) ++
      writeSuccessWithdrawalAddressBytes withdrawal ++ padding.
  { rewrite HrestShape in HrestSplit. rewrite HvalidatorBytes in HrestSplit.
    apply app_inv_head in HrestSplit. symmetry. exact HrestSplit. }
  have HamountBytes : amountBytes = writeSuccessWithdrawalIntegerBytes
      (observationWithdrawalAmount withdrawal).
  { pose proof (f_equal (firstn 8) HamountSplit) as H.
    rewrite HafterValidatorShape in H.
    rewrite firstn_app writeSuccessWithdrawalIntegerBytesLength in H.
    rewrite firstn_all2 in H.
    2: { rewrite writeSuccessWithdrawalIntegerBytesLength. lia. }
    rewrite Nat.sub_diag firstn_O app_nil_r in H.
    rewrite firstn_app HamountLength in H.
    rewrite firstn_all2 in H; last lia.
    rewrite Nat.sub_diag firstn_O app_nil_r in H. symmetry. exact H. }
  rewrite HamountBytes in Hamount.
  have Haddress : bv_unsigned (writeSuccess156d0Address sp) =
      bv_unsigned (sp + BV 64 1744)%bv + 16.
  { unfold writeSuccess156d0Address.
    have Hupper : bv_unsigned sp + 1792 < 0x40000000 by
      (unfold Inv_15694 in Hinv; tauto).
    have Hbase := writeSuccessWithdrawalsPrefixDestinationUnsigned sp Hupper.
    rewrite Hbase. bv_solve. }
  unfold read_mem. rewrite Haddress.
  replace (bv_unsigned (sp + BV 64 1744)%bv + 16) with
      (bv_unsigned (sp + BV 64 1744)%bv + 8 + 8) by lia.
  rewrite Hamount.
  unfold writeSuccessWithdrawalsAmountValue,
    writeSuccessWithdrawalIntegerBytes. reflexivity.
Qed.

Lemma writeSuccessEncoderIntGlobal2ReadDisjoint global sp returnAddress value
    address loaded :
  islaMemoryRange (bv_unsigned sp - 16) 16 ->
  islaMemoryRangesDisjoint (bv_unsigned sp - 16) 16 address 8 ->
  read_mem global.(seq_mem) address 8 = Some loaded ->
  read_mem (writeSuccessEncoderIntGlobal2 global sp returnAddress value).(seq_mem)
    address 8 = Some loaded.
Proof.
  intros Hrange Hdisjoint Hread. unfold read_mem in *.
  rewrite writeSuccessEncoderIntGlobal2Memory.
  have Hlength : length (bv_to_little_endian 8 8 (bv_unsigned value)) = 8%nat by
    (rewrite length_bv_to_little_endian; lia).
  have HreturnLength : length (bv_to_little_endian 8 8
      (bv_unsigned returnAddress)) = 8%nat by
    (rewrite length_bv_to_little_endian; lia).
  rewrite (read_mem_list_write_mem_list_disjoint_eq _ _ _ _ 8).
  2: { rewrite Hlength. unfold islaMemoryRange in *. lia. }
  2: { rewrite Hlength. unfold islaMemoryRangesDisjoint in *. lia. }
  rewrite (read_mem_list_write_mem_list_disjoint_eq _ _ _ _ 8).
  2: { rewrite HreturnLength. unfold islaMemoryRange in *. lia. }
  2: { rewrite HreturnLength. unfold islaMemoryRangesDisjoint in *. lia. }
  exact Hread.
Qed.

Lemma writeSuccessWithdrawalsFinalAmountRead args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs global
    (firstValue secondValue : bv 64) outputRegs :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  let firstGlobal := writeSuccessEncoderIntGlobal2
    (writeSuccessWithdrawals156a8Global regs global sp pointer current) sp
    (Z_to_bv 64 0x156b4) firstValue in
  let secondGlobal := writeSuccessEncoderIntGlobal2 firstGlobal sp
    (Z_to_bv 64 0x156c0) secondValue in
  read_mem
    (writeSuccess101a0After (writeSuccessOutputRegs4 outputRegs) secondGlobal
      (Z_to_bv 64 0x156d0)).2.(seq_mem)
    (bv_unsigned (writeSuccess156d0Address sp)) 8 =
    Some (bv_to_bvn (writeSuccessWithdrawalsAmountValue withdrawal)).
Proof.
  intros Hinv. cbn -[writeSuccessEncoderIntGlobal2].
  have Hinitial := writeSuccessWithdrawals156a8AmountRead args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs global Hinv.
  have HspLower : 0x20000000 <= bv_unsigned sp - 16 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hrange : islaMemoryRange (bv_unsigned sp - 16) 16.
  { unfold islaMemoryRange. pose proof (bv_unsigned_in_range 64 sp).
    unfold bv_modulus in *. cbn in *. lia. }
  have Haddress : bv_unsigned (writeSuccess156d0Address sp) =
      bv_unsigned sp + 1760.
  { unfold writeSuccess156d0Address.
    have Hupper : bv_unsigned sp + 1792 < 0x40000000 by
      (unfold Inv_15694 in Hinv; tauto).
    bv_solve. }
  have Hdisjoint : islaMemoryRangesDisjoint (bv_unsigned sp - 16) 16
      (bv_unsigned (writeSuccess156d0Address sp)) 8.
  { unfold islaMemoryRangesDisjoint. rewrite Haddress. lia. }
  have Hfirst := writeSuccessEncoderIntGlobal2ReadDisjoint
    (writeSuccessWithdrawals156a8Global regs global sp pointer current) sp
    (Z_to_bv 64 0x156b4) firstValue
    (bv_unsigned (writeSuccess156d0Address sp))
    (bv_to_bvn (writeSuccessWithdrawalsAmountValue withdrawal))
    Hrange Hdisjoint Hinitial.
  have Hsecond := writeSuccessEncoderIntGlobal2ReadDisjoint
    (writeSuccessEncoderIntGlobal2
      (writeSuccessWithdrawals156a8Global regs global sp pointer current) sp
      (Z_to_bv 64 0x156b4) firstValue) sp
    (Z_to_bv 64 0x156c0) secondValue
    (bv_unsigned (writeSuccess156d0Address sp))
    (bv_to_bvn (writeSuccessWithdrawalsAmountValue withdrawal))
    Hrange Hdisjoint Hfirst.
  unfold writeSuccess101a0After. destruct (_ !! _) eqn:Hlookup; exact Hsecond.
Qed.

Print Assumptions writeSuccessWithdrawals156a8AmountRead.
Print Assumptions writeSuccessEncoderIntGlobal2ReadDisjoint.
Print Assumptions writeSuccessWithdrawalsFinalAmountRead.
