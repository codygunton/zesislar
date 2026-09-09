From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b4.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntCallerFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpyState.

Open Scope Z_scope.

Definition writeSuccessWithdrawalsValidatorValue
    (withdrawal : WriteSuccessWithdrawalObservation) : bv 64 :=
  Z_to_bv 64 (little_endian_to_bv 8
    (writeSuccessWithdrawalIntegerBytes
      (observationWithdrawalValidatorIndex withdrawal))).

Lemma writeSuccessWithdrawalsFirstEntryValidatorRead args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs global :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
    withdrawal = writeSuccess15d10Before regs global ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess156b4Address sp)) 8 =
    Some (bv_to_bvn (writeSuccessWithdrawalsValidatorValue withdrawal)).
Proof.
  intros Hinv Hprefix HfirstEntry.
  have Hcurrent := writeSuccessWithdrawals156a8DestinationRead args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    Hinv.
  have Hglobal :
      (writeSuccessWithdrawals156a8Global regs0 global0 sp pointer current).(seq_mem) =
      global.(seq_mem).
  { pose proof (f_equal snd HfirstEntry) as H. cbn in H.
    exact (f_equal seq_mem H). }
  rewrite Hglobal in Hcurrent.
  destruct (read_mem_list_split global.(seq_mem)
    (bv_unsigned (sp + BV 64 1744)%bv) 8 40 current Hcurrent) as
    (indexBytes & rest & Hsplit & HindexLength & HrestLength & Hindex & Hrest).
  destruct (read_mem_list_split global.(seq_mem)
    (bv_unsigned (sp + BV 64 1744)%bv + 8) 8 32 rest Hrest) as
    (validatorBytes & tail & HrestSplit & HvalidatorLength & HtailLength &
      Hvalidator & Htail).
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
  have HvalidatorBytes : validatorBytes = writeSuccessWithdrawalIntegerBytes
      (observationWithdrawalValidatorIndex withdrawal).
  { have HindexBytes : indexBytes = writeSuccessWithdrawalIntegerBytes
        (observationWithdrawalIndex withdrawal).
    { pose proof (f_equal (firstn 8) Hsplit) as H.
      rewrite HcurrentShape in H.
      rewrite firstn_app writeSuccessWithdrawalIntegerBytesLength in H.
      rewrite firstn_all2 in H.
      2: { rewrite writeSuccessWithdrawalIntegerBytesLength. lia. }
      rewrite Nat.sub_diag firstn_O app_nil_r in H.
      rewrite firstn_app HindexLength in H.
      rewrite firstn_all2 in H; last lia.
      rewrite Nat.sub_diag firstn_O app_nil_r in H.
      symmetry. exact H. }
    have HrestShape : rest =
        writeSuccessWithdrawalIntegerBytes
          (observationWithdrawalValidatorIndex withdrawal) ++
        writeSuccessWithdrawalIntegerBytes
          (observationWithdrawalAmount withdrawal) ++
        writeSuccessWithdrawalAddressBytes withdrawal ++ padding.
    { rewrite HcurrentShape in Hsplit. rewrite HindexBytes in Hsplit.
      apply app_inv_head in Hsplit. symmetry. exact Hsplit. }
    rewrite HrestSplit in HrestShape.
    pose proof (f_equal (firstn 8) HrestShape) as H.
    rewrite firstn_app HvalidatorLength in H.
    rewrite firstn_all2 in H; last lia.
    rewrite Nat.sub_diag firstn_O app_nil_r in H.
    rewrite firstn_app writeSuccessWithdrawalIntegerBytesLength in H.
    rewrite firstn_all2 in H.
    2: { rewrite writeSuccessWithdrawalIntegerBytesLength. lia. }
    rewrite Nat.sub_diag firstn_O app_nil_r in H.
    exact H. }
  rewrite HvalidatorBytes in Hvalidator.
  have Haddress : bv_unsigned (writeSuccess156b4Address sp) =
      bv_unsigned (sp + BV 64 1744)%bv + 8.
  { unfold writeSuccess156b4Address.
    have Hupper : bv_unsigned sp + 1792 < 0x40000000 by
      (unfold Inv_15694 in Hinv; tauto).
    have Hbase := writeSuccessWithdrawalsPrefixDestinationUnsigned sp Hupper.
    rewrite Hbase. bv_solve. }
  unfold read_mem. rewrite Haddress Hvalidator.
  unfold writeSuccessWithdrawalsValidatorValue,
    writeSuccessWithdrawalIntegerBytes.
  reflexivity.
Qed.

Lemma writeSuccessWithdrawalsFirstEndpointValidatorRead args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs global :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
    withdrawal = writeSuccess15d10Before regs global ->
  read_mem
    (writeSuccessWithdrawalsEncoderIntEndpoint regs global sp
      (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)).2.(seq_mem)
    (bv_unsigned (writeSuccess156b4Address sp)) 8 =
    Some (bv_to_bvn (writeSuccessWithdrawalsValidatorValue withdrawal)).
Proof.
  intros Hinv Hprefix Hentry.
  have Hread := writeSuccessWithdrawalsFirstEntryValidatorRead args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    regs global Hinv Hprefix Hentry.
  have HfirstInv := writeSuccessWithdrawals156a8EncoderIntInv args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 Hinv Hprefix.
  rewrite Hentry in HfirstInv.
  have Htable : writeSuccessWithdrawalsInstructionTable global by
    (unfold Inv_encoder_int in HfirstInv; cbn in HfirstInv; tauto).
  destruct (writeSuccessEncoderIntCaller156b4 global Htable) as
    (Halign & returnTrace & Hreturn).
  rewrite (writeSuccessWithdrawalsEncoderIntEndpointGlobal regs global sp
    (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)
    returnTrace Halign Hreturn).
  unfold read_mem in *.
  rewrite writeSuccessEncoderIntGlobal2Memory.
  have HspLower : 0x20000000 <= bv_unsigned sp - 16 by
    (unfold Inv_15694 in Hinv; tauto).
  have HspUpper : bv_unsigned sp + 1792 < 0x40000000 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hrange : islaMemoryRange (bv_unsigned sp - 16) 16.
  { unfold islaMemoryRange. pose proof (bv_unsigned_in_range 64 sp).
    unfold bv_modulus in *. cbn in *. lia. }
  have Haddress : bv_unsigned (writeSuccess156b4Address sp) =
      bv_unsigned sp + 1752.
  { unfold writeSuccess156b4Address. bv_solve. }
  rewrite Haddress in Hread |- *.
  have HvalueLength : length (bv_to_little_endian 8 8
      (bv_unsigned (writeSuccessWithdrawalsIndexValue withdrawal))) = 8%nat by
    (rewrite length_bv_to_little_endian; lia).
  have HreturnLength : length (bv_to_little_endian 8 8
      (bv_unsigned (Z_to_bv 64 0x156b4))) = 8%nat by
    (rewrite length_bv_to_little_endian; lia).
  rewrite (read_mem_list_write_mem_list_disjoint_eq _ _ _ _ 8).
  2: { rewrite HvalueLength. unfold islaMemoryRange in *. lia. }
  2: { rewrite HvalueLength. unfold islaMemoryRangesDisjoint. lia. }
  rewrite (read_mem_list_write_mem_list_disjoint_eq _ _ _ _ 8).
  2: { rewrite HreturnLength. unfold islaMemoryRange in *. lia. }
  2: { rewrite HreturnLength. unfold islaMemoryRangesDisjoint. lia. }
  exact Hread.
Qed.

Print Assumptions writeSuccessWithdrawalsFirstEntryValidatorRead.
Print Assumptions writeSuccessWithdrawalsFirstEndpointValidatorRead.
