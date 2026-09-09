From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyByteRun.

Open Scope Z_scope.

Lemma writeSuccessMemcpyAddressAt (base : bv 64) index total :
  0 <= index <= total ->
  bv_unsigned base + total <= 0x40000000 ->
  bv_unsigned (base + Z_to_bv 64 index)%bv = bv_unsigned base + index.
Proof.
  intros Hindex Hupper. rewrite bv_add_unsigned Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 64 base) as HbaseRange.
  have HindexSmall : 0 <= index < bv_modulus 64.
  { unfold bv_modulus. cbn. lia. }
  have HsumSmall : 0 <= bv_unsigned base + index < bv_modulus 64.
  { unfold bv_modulus in *. cbn in *. lia. }
  rewrite (bv_wrap_small 64 index HindexSmall).
  rewrite (bv_wrap_small 64 _ HsumSmall). reflexivity.
Qed.

Lemma writeSuccessMemcpyAddressAtBv (base : bv 64) index total :
  0 <= index <= total ->
  bv_unsigned base + total <= 0x40000000 ->
  (base + Z_to_bv 64 index)%bv =
    Z_to_bv 64 (bv_unsigned base + index).
Proof.
  intros Hindex Hupper. apply bv_eq.
  rewrite (writeSuccessMemcpyAddressAt base index total); try assumption.
  rewrite Z_to_bv_unsigned bv_wrap_small; first reflexivity.
  pose proof (bv_unsigned_in_range 64 base).
  unfold bv_modulus in *. cbn in *. lia.
Qed.

Lemma writeSuccessMemcpyOneByteDisjoint (destination source : Z)
    (index total : nat) :
  (index < total)%nat ->
  islaMemoryRangesDisjoint destination total source total ->
  islaMemoryRangesDisjoint (destination + Z.of_nat index) 1 source total.
Proof.
  unfold islaMemoryRangesDisjoint. cbn. intros Hindex Hdisjoint.
  destruct Hdisjoint; [left | right]; lia.
Qed.

Lemma writeSuccessMemcpyIndexDifferent index total :
  0 <= index < total ->
  total < 2 ^ 64 ->
  Z_to_bv 64 index <> Z_to_bv 64 total.
Proof.
  intros Hindex Htotal Heq. apply (f_equal bv_unsigned) in Heq.
  rewrite !Z_to_bv_unsigned !bv_wrap_small in Heq;
    unfold bv_modulus in *; cbn in *; lia.
Qed.

Print Assumptions writeSuccessMemcpyAddressAt.
Print Assumptions writeSuccessMemcpyAddressAtBv.
Print Assumptions writeSuccessMemcpyOneByteDisjoint.
Print Assumptions writeSuccessMemcpyIndexDifferent.
