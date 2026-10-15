Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Contracts.AltFlFree.
From Coq Require Import ZArith Lia.
Open Scope Z_scope.

Lemma freeSizeClassOfBytesRange size :
  0 <= freeSizeClassOfBytes size <= 22.
Proof.
  unfold freeSizeClassOfBytes.
  repeat match goal with |- context [if ?condition then _ else _] => destruct condition end;
    lia.
Qed.

Lemma freeSmallAlignmentClass size alignment : alignment <= 3 ->
  freeSizeClass size alignment = freeSizeClassOfBytes size.
Proof.
  intros Halign. pose proof (freeSizeClassOfBytesRange size) as Hrange.
  unfold freeSizeClass.
  assert (Hzero : Z.max 0 (alignment - 3) = 0) by (apply Z.max_l; lia).
  rewrite Hzero. apply Z.max_l. lia.
Qed.

Lemma freeSizeClassOfBytesAcceptingRange size (classWord : bv 64) :
  classWord = Z_to_bv 64 (freeSizeClassOfBytes size) ->
  ~ bv_signed (bv_zero_extend 128 classWord) >=
    bv_signed (bv_zero_extend 128 (BV 64 22)) ->
  0 <= freeSizeClassOfBytes size < 22.
Proof.
  intros Hword Hguard.
  pose proof (freeSizeClassOfBytesRange size) as Hrange.
  assert (Hfits : 0 <= freeSizeClassOfBytes size < bv_modulus 64).
  { unfold bv_modulus. cbn. lia. }
  rewrite Hword !zesu_signed_zero_extend_64_128 in Hguard.
  rewrite (Z_to_bv_small 64 _ Hfits) in Hguard.
  change (~ freeSizeClassOfBytes size >= 22) in Hguard.
  lia.
Qed.
