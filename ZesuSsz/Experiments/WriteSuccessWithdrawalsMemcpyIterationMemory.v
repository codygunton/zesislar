From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f0.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyByteRun.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessMemcpyStoredByte (byte : bv 8) :
  writeSuccess101f0Bytes (writeSuccess101e4Loaded byte) = [byte].
Proof.
  have Hlookup :
      writeSuccess101f0Bytes (writeSuccess101e4Loaded byte) !! 0%nat = Some byte.
  { unfold writeSuccess101f0Bytes, writeSuccess101f0Byte,
      writeSuccess101e4Loaded.
    apply (proj2 (bv_to_little_endian_lookup_Some 1 8
      (bv_unsigned (bv_extract 0 8 (bv_zero_extend 64 byte))) 0 byte
      ltac:(lia))).
    split; first lia. apply bv_eq. bv_solve. }
  have Hlength :
      length (writeSuccess101f0Bytes (writeSuccess101e4Loaded byte)) = 1%nat.
  { unfold writeSuccess101f0Bytes. rewrite length_bv_to_little_endian; lia. }
  destruct (writeSuccess101f0Bytes (writeSuccess101e4Loaded byte)) as
    [|head tail] eqn:Hbytes; cbn in Hlookup; first discriminate.
  inversion Hlookup. subst head. destruct tail; cbn in Hlength; congruence.
Qed.

Lemma writeSuccessMemcpyWriteSingleton mem destination prefix byte :
  islaMemoryRange (bv_unsigned destination) (S (length prefix)) ->
  write_mem_list
    (write_mem_list mem destination prefix)
    (destination `+Z` Z.of_nat (length prefix)) [byte] =
  write_mem_list mem destination (prefix ++ [byte]).
Proof.
  revert mem destination.
  induction prefix as [|head prefix IH]; intros mem destination Hrange.
  - cbn. rewrite bv_add_Z_0. reflexivity.
  - cbn [app length write_mem_list].
    replace ((destination `+Z` Z.of_nat (S (length prefix)))%bv) with
      (((destination `+Z` 1) `+Z` Z.of_nat (length prefix))%bv) by
      (apply bv_eq; bv_solve).
    apply IH. unfold islaMemoryRange in Hrange |- *.
    rewrite bv_add_Z_unsigned.
    have Hsmall : 0 <= bv_unsigned destination + 1 < bv_modulus 64.
    { pose proof (bv_unsigned_in_range 64 destination).
      unfold bv_modulus in *. cbn in *. lia. }
    rewrite (bv_wrap_small 64 _ Hsmall). cbn in Hrange |- *. lia.
Qed.

Print Assumptions writeSuccessMemcpyStoredByte.
Print Assumptions writeSuccessMemcpyWriteSingleton.
