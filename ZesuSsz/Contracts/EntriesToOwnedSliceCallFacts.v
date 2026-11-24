From Coq Require Import List ZArith Lia.
From stdpp Require Import base list bitvector.definitions.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceCallSpec2.
Open Scope Z_scope.

(* The facts a caller of entriesToOwnedSlice reads from the sealed call facts
   (registry ZesuSsz/Contracts/proved_functions.json, interface lemmas of the
   row entriesToOwnedSlice). Each is stated over the template's predicates; inside
   the sealed module the sealed predicates are these definitions. *)

Lemma entriesToOwnedSliceDomainIntro argv context state resultBefore scratchBefore :
  entriesToOwnedSliceBoundaryDomain argv context state resultBefore scratchBefore ->
  entriesToOwnedSliceBoundaryDomain argv context state resultBefore scratchBefore.
Proof. exact id. Qed.

(* The result slot a call site passes holds 24 bytes: the length a caller
   carves out of an uninitialised frame region for it. *)
Lemma entriesToOwnedSliceDomainResultLength argv context state resultBefore scratchBefore :
  entriesToOwnedSliceBoundaryDomain argv context state resultBefore scratchBefore ->
  length resultBefore = 24%nat.
Proof. intros (_ & _ & _ & _ & _ & _ & _ & Hlen & _). lia. Qed.

Lemma entriesToOwnedSliceAllowsWellFormed state resultBefore outcome :
  entriesToOwnedSliceBoundaryAllows state resultBefore outcome ->
  arrayListWellFormed entriesElementBytes (toOwnedListAfter outcome) /\
  arrayListWellFormed entriesElementBytes (toOwnedSlice outcome) /\
  arrayListCapacity (toOwnedSlice outcome) = arrayListLength (toOwnedSlice outcome).
Proof. intros (? & ? & ? & _). auto. Qed.

Lemma entriesToOwnedSliceAllowsEmpty state resultBefore outcome :
  entriesToOwnedSliceBoundaryAllows state resultBefore outcome ->
  arrayListLength state = 0 ->
  toOwnedKind outcome = arrayListSuccess /\
  toOwnedListAfter outcome = arrayListEmpty entriesEmptyPointer /\
  toOwnedSlice outcome = arrayListEmpty (arrayListPointer state) /\
  toOwnedResultAfter outcome = arrayListResultImage resultBefore (arrayListPointer state) 0.
Proof.
  intros (_ & _ & _ & H) Hzero. cbn in H. rewrite Hzero in H. exact H.
Qed.

Lemma entriesToOwnedSliceAllowsSuccess state resultBefore outcome :
  entriesToOwnedSliceBoundaryAllows state resultBefore outcome ->
  arrayListLength state <> 0 ->
  toOwnedKind outcome = arrayListSuccess ->
  toOwnedListAfter outcome = arrayListEmpty (arrayListPointer state) /\
  arrayListLength (toOwnedSlice outcome) = arrayListLength state /\
  arrayListItems (toOwnedSlice outcome) = arrayListItems state /\
  toOwnedResultAfter outcome =
    arrayListResultImage resultBefore (arrayListPointer (toOwnedSlice outcome)) (arrayListLength state).
Proof.
  intros (_ & _ & _ & H) Hlen Hkind. cbn in H.
  apply Z.eqb_neq in Hlen. rewrite Hlen, Hkind in H. exact H.
Qed.

Lemma entriesToOwnedSliceAllowsOutOfMemory state resultBefore outcome :
  entriesToOwnedSliceBoundaryAllows state resultBefore outcome ->
  arrayListLength state <> 0 ->
  toOwnedKind outcome = arrayListOutOfMemory ->
  toOwnedListAfter outcome = state /\
  toOwnedSlice outcome = arrayListEmpty entriesEmptyPointer /\
  toOwnedResultAfter outcome = arrayListErrorImage resultBefore arrayListOutOfMemoryCode.
Proof.
  intros (_ & _ & _ & H) Hlen Hkind. cbn in H.
  apply Z.eqb_neq in Hlen. rewrite Hlen, Hkind in H. exact H.
Qed.

Lemma entriesToOwnedSliceAllowsLink state resultBefore outcome :
  entriesToOwnedSliceBoundaryAllows state resultBefore outcome ->
  entriesToOwnedSliceBoundaryAllows state resultBefore outcome.
Proof. exact id. Qed.
