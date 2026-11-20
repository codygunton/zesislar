Require Import ZesuSsz.Automation2.DomainRanges.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Contracts.ZiskRuntime.
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

(* The memcpy tail transfers copy the 80 result bytes to the result pointer;
   the runtime's domain of that copy follows from the result range. *)
Lemma parentHeaderResultMemcpyDomain (args : ParentHeaderArgs) :
  parentHeaderArgsWellFormed args ->
  parentHeaderMemcpyDomain (bv_unsigned (parentHeaderResultPointer args)).
Proof.
  intros Hwf. destruct (parentHeaderResultRange args Hwf) as [Hlow Hhigh].
  unfold parentHeaderMemcpyDomain, ziskMemcpyRange, ziskWord, stockZiskPermissions.
  cbn [ziskReadableSection ziskWritableSection].
  split; [lia |]. split.
  { apply Exists_cons_tl, Exists_cons_hd. cbn. split; [reflexivity | lia]. }
  split.
  { cbn. split; [lia |]. split; [lia |].
    repeat (apply Forall_cons; [cbn; first [left; reflexivity | right; lia] |]).
    apply Forall_nil. }
  cbn. split; [lia |]. split; [lia |].
  repeat (apply Forall_cons; [cbn; first [left; reflexivity | right; lia] |]).
  apply Forall_nil.
Qed.

(* The alignment fact is not posed: a symbolic `mod` in the context makes
   every failing `lia` search branch on its quotient. A rule that needs it
   applies `parentHeaderStackAligned`. The memcpy domain stays folded: the
   tail transfers request it as one fact. *)
#[export] Instance parentHeaderDomainRanges (args : ParentHeaderArgs) :
  ZesuDomainRanges (parentHeaderArgsWellFormed args)
    ((2684355072 <= bv_unsigned (parentHeaderStackPointer args) < 3221225472) /\
     (2684354560 <= bv_unsigned (parentHeaderResultPointer args) /\
      bv_unsigned (parentHeaderResultPointer args) + 80 <= 3221225472) /\
     (1073741824 <= bv_unsigned (parentHeaderInputPointer args) /\
      bv_unsigned (parentHeaderInputPointer args) +
        Z.of_nat (length (parentHeaderInputBytes args)) <= 2147483648) /\
     Z.of_nat (length (parentHeaderInputBytes args)) < 18446744073709551607 /\
     parentHeaderMemcpyDomain (bv_unsigned (parentHeaderResultPointer args)) /\
     Z.of_nat (length (parentHeaderInputBytes args)) = bv_unsigned (parentHeaderInputLength args)).
Proof.
  intros Hwf. split; [|split; [|split; [|split; [|split]]]].
  - pose proof (parentHeaderStackRange args Hwf). lia.
  - exact (parentHeaderResultRange args Hwf).
  - exact (parentHeaderInputRange args Hwf).
  - exact (parentHeaderInputSmall args Hwf).
  - exact (parentHeaderResultMemcpyDomain args Hwf).
  - exact (proj1 Hwf).
Qed.
