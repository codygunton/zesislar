From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.

Open Scope Z_scope.

Lemma writeSuccessEncoderIntAfterStoresReturnBytes global
    (sp returnAddress value : bv 64) :
  islaMemoryRange (bv_unsigned sp - 16) 16 ->
  read_mem_list
    (writeSuccessEncoderIntGlobal2 global sp returnAddress value).(seq_mem)
    (bv_unsigned sp - 8) 8%N =
    Some (bv_to_little_endian 8 8 (bv_unsigned returnAddress)).
Proof.
  intros Hrange. rewrite writeSuccessEncoderIntGlobal2Memory.
  have HvalueLength :
      length (bv_to_little_endian 8 8 (bv_unsigned value)) = 8%nat by
    (rewrite length_bv_to_little_endian; lia).
  have HreturnLength :
      length (bv_to_little_endian 8 8 (bv_unsigned returnAddress)) = 8%nat by
    (rewrite length_bv_to_little_endian; lia).
  have HvalueRange : islaMemoryRange (bv_unsigned sp - 16)
      (length (bv_to_little_endian 8 8 (bv_unsigned value))).
  { rewrite HvalueLength. unfold islaMemoryRange in *. lia. }
  have HreturnRange : islaMemoryRange (bv_unsigned sp - 8)
      (length (bv_to_little_endian 8 8 (bv_unsigned returnAddress))).
  { rewrite HreturnLength. unfold islaMemoryRange in *. lia. }
  have Hdisjoint : islaMemoryRangesDisjoint (bv_unsigned sp - 16)
      (length (bv_to_little_endian 8 8 (bv_unsigned value)))
      (bv_unsigned sp - 8) 8.
  { rewrite HvalueLength. unfold islaMemoryRangesDisjoint. lia. }
  rewrite (read_mem_list_write_mem_list_disjoint_eq
    (write_mem_list global.(seq_mem) (Z_to_bv 64 (bv_unsigned sp - 8))
      (bv_to_little_endian 8 8 (bv_unsigned returnAddress)))
    (bv_unsigned sp - 16)
    (bv_to_little_endian 8 8 (bv_unsigned value))
    (bv_unsigned sp - 8) 8 HvalueRange Hdisjoint).
  rewrite <- HreturnLength.
  apply read_mem_list_written. exact HreturnRange.
Qed.

Theorem writeSuccessEncoderIntAfterStoresScratch global
    (sp returnAddress value : bv 64) :
  islaMemoryRange (bv_unsigned sp - 16) 16 ->
  read_mem_list
    (writeSuccessEncoderIntGlobal2 global sp returnAddress value).(seq_mem)
    (bv_unsigned sp - 16) 16%N =
    Some
      (bv_to_little_endian 8 8 (bv_unsigned value) ++
       bv_to_little_endian 8 8 (bv_unsigned returnAddress)).
Proof.
  intros Hrange.
  have Hlow := writeSuccessEncoderIntAfterStoresValue global sp returnAddress
    value Hrange.
  have Hhigh := writeSuccessEncoderIntAfterStoresReturnBytes global sp
    returnAddress value Hrange.
  have Happ := read_mem_list_append
    (writeSuccessEncoderIntGlobal2 global sp returnAddress value).(seq_mem)
    (bv_unsigned sp - 16) 8 8
    (bv_to_little_endian 8 8 (bv_unsigned value))
    (bv_to_little_endian 8 8 (bv_unsigned returnAddress)) Hlow.
  replace (bv_unsigned sp - 16 + Z.of_nat 8) with (bv_unsigned sp - 8) in Happ
    by lia.
  specialize (Happ Hhigh).
  exact Happ.
Qed.

Print Assumptions writeSuccessEncoderIntAfterStoresReturnBytes.
Print Assumptions writeSuccessEncoderIntAfterStoresScratch.

