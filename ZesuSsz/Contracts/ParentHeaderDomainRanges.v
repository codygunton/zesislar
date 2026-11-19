Require Import ZesuSsz.Automation2.DomainRanges.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
From Coq Require Import List ZArith.ZArith Lia.
From stdpp Require Import bitvector.definitions.
Open Scope Z_scope.

(* The pointer ranges of decodeParentHeader's domain, read off
   `parentHeaderArgsWellFormed`. The domain stays folded in a block's
   context; `zesu_pose_domain_ranges` poses the registered ranges beside it. *)

Lemma parentHeaderStackRange (args : ParentHeaderArgs) :
  parentHeaderArgsWellFormed args ->
  2684354560 + 400 + 112 <= bv_unsigned (parentHeaderStackPointer args) < 3221225472.
Proof.
  unfold parentHeaderArgsWellFormed.
  intros (_&_&_&_&_&_&_&_&_&_&Hlow&Hhigh&_). split; assumption.
Qed.

Lemma parentHeaderStackAligned (args : ParentHeaderArgs) :
  parentHeaderArgsWellFormed args ->
  bv_unsigned (parentHeaderStackPointer args) mod 16 = 0.
Proof.
  unfold parentHeaderArgsWellFormed.
  intros (_&_&_&_&_&_&_&_&_&_&_&_&Haligned&_). exact Haligned.
Qed.

Lemma parentHeaderResultRange (args : ParentHeaderArgs) :
  parentHeaderArgsWellFormed args ->
  2684354560 <= bv_unsigned (parentHeaderResultPointer args) /\
  bv_unsigned (parentHeaderResultPointer args) + 80 <= 3221225472.
Proof.
  unfold parentHeaderArgsWellFormed.
  intros (_&_&_&_&_&_&_&_&Hlow&Hhigh&_). split; assumption.
Qed.

Lemma parentHeaderInputRange (args : ParentHeaderArgs) :
  parentHeaderArgsWellFormed args ->
  1073741824 <= bv_unsigned (parentHeaderInputPointer args) /\
  bv_unsigned (parentHeaderInputPointer args) +
    Z.of_nat (length (parentHeaderInputBytes args)) <= 2147483648.
Proof.
  unfold parentHeaderArgsWellFormed.
  intros (Hlength&_&_&_&_&Hlow&Hhigh&_). rewrite Hlength. split; assumption.
Qed.

Lemma parentHeaderInputSmall (args : ParentHeaderArgs) :
  parentHeaderArgsWellFormed args ->
  Z.of_nat (length (parentHeaderInputBytes args)) < 18446744073709551607.
Proof.
  intros Hwf. pose proof (parentHeaderInputRange args Hwf). lia.
Qed.

(* The alignment fact is not posed: a symbolic `mod` in the context makes
   every failing `lia` search branch on its quotient. A rule that needs it
   applies `parentHeaderStackAligned`. *)
#[export] Instance parentHeaderDomainRanges (args : ParentHeaderArgs) :
  ZesuDomainRanges (parentHeaderArgsWellFormed args)
    ((2684355072 <= bv_unsigned (parentHeaderStackPointer args) < 3221225472) /\
     (2684354560 <= bv_unsigned (parentHeaderResultPointer args) /\
      bv_unsigned (parentHeaderResultPointer args) + 80 <= 3221225472) /\
     (1073741824 <= bv_unsigned (parentHeaderInputPointer args) /\
      bv_unsigned (parentHeaderInputPointer args) +
        Z.of_nat (length (parentHeaderInputBytes args)) <= 2147483648) /\
     Z.of_nat (length (parentHeaderInputBytes args)) < 18446744073709551607).
Proof.
  intros Hwf. split; [|split; [|split]].
  - pose proof (parentHeaderStackRange args Hwf). lia.
  - exact (parentHeaderResultRange args Hwf).
  - exact (parentHeaderInputRange args Hwf).
  - exact (parentHeaderInputSmall args Hwf).
Qed.
