Require Import ZesuSsz.Automation.All.
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

