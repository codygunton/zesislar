From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyAfter.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpyMemory.

Open Scope Z_scope.

Lemma writeSuccessWithdrawals156a8DestinationRead args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs global :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  read_mem_list
      (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_mem)
      (bv_unsigned (sp + BV 64 1744)%bv) 48%N = Some current.
Proof.
  intros Hinv.
  have Hlength : length current = 48%nat by
    (unfold Inv_15694 in Hinv; tauto).
  destruct (writeSuccessWithdrawalsPrefix15694MemcpyMemory args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state Hinv) as
    (_ & _ & Hrange & _ & _ & Hlower & Hupper & _ & Hbacked & _).
  have Hmemory := writeSuccessMemcpyBytesAfterMemory
    (writeSuccess101d4Regs regs) global pointer (sp + BV 64 1744)%bv
    (Z_to_bv 64 0) current 0 ltac:(reflexivity) ltac:(lia).
  specialize (Hmemory ltac:(rewrite Hlength; cbn; lia)).
  unfold writeSuccessWithdrawals156a8Global, writeSuccessMemcpyEndpointGlobal,
    writeSuccessMemcpyLoopAfter.
  rewrite Hmemory.
  replace ((sp + BV 64 1744)%bv + Z_to_bv 64 0)%bv with
      (Z_to_bv 64 (bv_unsigned (sp + BV 64 1744)%bv)) by
    (apply bv_eq; bv_solve).
  pose proof (read_mem_list_written (seq_mem global)
    (bv_unsigned (sp + BV 64 1744)%bv) current Hrange) as Hwritten.
  rewrite Hlength in Hwritten. exact Hwritten.
Qed.

Lemma writeSuccessWithdrawals156a8IndexRead args sp pointer base total processed
    remaining withdrawal allBytes prefix current suffix scratch encoderScratch
    registerFrame memoryFrame priorLog state regs global :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  read_mem_list
      (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_mem)
      (bv_unsigned (sp + BV 64 1744)%bv) 48%N = Some current ->
  read_mem
      (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_mem)
      (bv_unsigned (writeSuccess156a8Address sp)) 8 =
    Some (bv_to_bvn (writeSuccessWithdrawalsIndexValue withdrawal)).
Proof.
  intros Hinv Hread.
  destruct (Inv_15694_current_shape args sp pointer base total processed remaining
    withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state Hinv) as (padding & Hpadding & Hcurrent).
  destruct (read_mem_list_split _ _ 8 40 current Hread) as
    (indexBytes & rest & Hsplit & HindexLength & HrestLength & Hindex & Hrest).
  have HindexBytes : indexBytes = writeSuccessWithdrawalIntegerBytes
      (observationWithdrawalIndex withdrawal).
  { pose proof (f_equal (firstn 8) Hsplit) as Hfirst.
    rewrite Hcurrent in Hfirst. unfold writeSuccessWithdrawalRawBytes in Hfirst.
    rewrite firstn_app writeSuccessWithdrawalIntegerBytesLength Nat.sub_diag
      firstn_O app_nil_r in Hfirst.
    rewrite firstn_app HindexLength Nat.sub_diag firstn_O app_nil_r in Hfirst.
    have Hleft : firstn 8 (writeSuccessWithdrawalIntegerBytes
        (observationWithdrawalIndex withdrawal)) =
        writeSuccessWithdrawalIntegerBytes (observationWithdrawalIndex withdrawal).
    { apply firstn_all2. rewrite writeSuccessWithdrawalIntegerBytesLength. lia. }
    have Hright : firstn 8 indexBytes = indexBytes.
    { apply firstn_all2. rewrite HindexLength. lia. }
    rewrite Hleft Hright in Hfirst.
    symmetry. exact Hfirst. }
  rewrite HindexBytes in Hindex.
  pose proof (read_mem_list_to_read_mem _ _ _ _ Hindex) as Hmemory.
  unfold writeSuccess156a8Address, writeSuccessWithdrawalsIndexValue,
    writeSuccessWithdrawalIntegerBytes in *.
  exact Hmemory.
Qed.

Print Assumptions writeSuccessWithdrawals156a8IndexRead.
Print Assumptions writeSuccessWithdrawals156a8DestinationRead.
