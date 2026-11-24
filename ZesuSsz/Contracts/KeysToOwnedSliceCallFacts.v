From Coq Require Import List ZArith Lia.
From stdpp Require Import base list bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceCallSpec2.
Open Scope Z_scope.

(* The facts a caller of keysToOwnedSlice reads from the sealed call facts
   (registry ZesuSsz/Contracts/proved_functions.json, interface lemmas of the
   row keysToOwnedSlice). Each is stated over the template's predicates; inside
   the sealed module the sealed predicates are these definitions. *)

Lemma keysToOwnedSliceDomainIntro argv context state resultBefore scratchBefore :
  keysToOwnedSliceBoundaryDomain argv context state resultBefore scratchBefore ->
  keysToOwnedSliceBoundaryDomain argv context state resultBefore scratchBefore.
Proof. exact id. Qed.

(* The result slot a call site passes holds 24 bytes: the length a caller
   carves out of an uninitialised frame region for it. *)
Lemma keysToOwnedSliceDomainResultLength argv context state resultBefore scratchBefore :
  keysToOwnedSliceBoundaryDomain argv context state resultBefore scratchBefore ->
  length resultBefore = 24%nat.
Proof. intros (_ & _ & _ & _ & _ & _ & _ & Hlen & _). lia. Qed.

Lemma keysToOwnedSliceAllowsWellFormed state resultBefore outcome :
  keysToOwnedSliceBoundaryAllows state resultBefore outcome ->
  arrayListWellFormed keysElementBytes (toOwnedListAfter outcome) /\
  arrayListWellFormed keysElementBytes (toOwnedSlice outcome) /\
  arrayListCapacity (toOwnedSlice outcome) = arrayListLength (toOwnedSlice outcome).
Proof. intros (? & ? & ? & _). auto. Qed.

Lemma keysToOwnedSliceAllowsEmpty state resultBefore outcome :
  keysToOwnedSliceBoundaryAllows state resultBefore outcome ->
  arrayListLength state = 0 ->
  toOwnedKind outcome = arrayListSuccess /\
  toOwnedListAfter outcome = arrayListEmpty keysEmptyPointer /\
  toOwnedSlice outcome = arrayListEmpty (arrayListPointer state) /\
  toOwnedResultAfter outcome = arrayListResultImage resultBefore (arrayListPointer state) 0.
Proof.
  intros (_ & _ & _ & H) Hzero. cbn in H. rewrite Hzero in H. exact H.
Qed.

Lemma keysToOwnedSliceAllowsSuccess state resultBefore outcome :
  keysToOwnedSliceBoundaryAllows state resultBefore outcome ->
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

Lemma keysToOwnedSliceAllowsOutOfMemory state resultBefore outcome :
  keysToOwnedSliceBoundaryAllows state resultBefore outcome ->
  arrayListLength state <> 0 ->
  toOwnedKind outcome = arrayListOutOfMemory ->
  toOwnedListAfter outcome = state /\
  toOwnedSlice outcome = arrayListEmpty keysEmptyPointer /\
  toOwnedResultAfter outcome = arrayListErrorImage resultBefore arrayListOutOfMemoryCode.
Proof.
  intros (_ & _ & _ & H) Hlen Hkind. cbn in H.
  apply Z.eqb_neq in Hlen. rewrite Hlen, Hkind in H. exact H.
Qed.

Lemma keysToOwnedSliceAllowsLink state resultBefore outcome :
  keysToOwnedSliceBoundaryAllows state resultBefore outcome ->
  keysToOwnedSliceBoundaryAllows state resultBefore outcome.
Proof. exact id. Qed.
