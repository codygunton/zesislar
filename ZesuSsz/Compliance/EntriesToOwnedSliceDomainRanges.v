From Coq Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import ZesuSsz.Automation2.DomainRanges.
Require Export ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Open Scope Z_scope.

(* The ranges and links of the folded entriesToOwnedSlice block domain as plain
   facts (DomainRanges.v). The alignment facts stay folded: a symbolic `mod`
   in the context makes every failing `lia` search branch on its quotient.
   `toOwnedSliceDomain` is posed as a fact so that its own instance
   (ArrayListContract.v) adds its ranges. *)
Lemma entriesBlockDomainRanges (returnAddress : Z) (args : EntriesToOwnedSliceBlockArgs) :
  entriesBlockDomainAt returnAddress args ->
  bv_unsigned (toOwnedReturnAddress (entriesBase args)) = returnAddress /\
  0 <= returnAddress < 2 ^ 64 /\
  0 <= arrayListLength (entriesBlockList args) <= 2 ^ 24 /\
  0 <= arrayListCapacity (entriesBlockList args) <= 2 ^ 24 /\
  arrayListLength (entriesBlockList args) <= arrayListCapacity (entriesBlockList args) /\
  1 <= arrayListPointer (entriesBlockList args) < 2 ^ 64 /\
  Z.of_nat (length (arrayListItems (entriesBlockList args))) =
    arrayListLength (entriesBlockList args) * entriesElementBytes /\
  toOwnedSliceDomain entriesElementBytes (entriesBase args) /\
  entriesBlockRamLow <= bv_unsigned (toOwnedResultPointer (entriesBase args)) /\
  bv_unsigned (toOwnedResultPointer (entriesBase args)) + entriesBlockResultBytes <=
    entriesBlockRamHigh /\
  entriesBlockRamLow <= bv_unsigned (toOwnedListPointer (entriesBase args)) /\
  bv_unsigned (toOwnedListPointer (entriesBase args)) + entriesBlockHeaderBytes <=
    entriesBlockRamHigh /\
  entriesBlockRamLow <= bv_unsigned (toOwnedAllocatorPointer (entriesBase args)) /\
  bv_unsigned (toOwnedAllocatorPointer (entriesBase args)) + entriesBlockAllocatorBytes <=
    entriesBlockRamHigh /\
  entriesBlockRamLow + entriesBlockFrameBytes + entriesBlockCalleeBytes <=
    bv_unsigned (toOwnedStackPointer (entriesBase args)) <= entriesBlockRamHigh.
Proof.
  unfold entriesBlockDomainAt, entriesBlockArgsWellFormed.
  intros [<- H].
  pose proof (bv_unsigned_in_range _ (toOwnedReturnAddress (entriesBase args))) as Hrange.
  change (bv_modulus 64) with (2 ^ 64) in Hrange.
  intuition lia.
Qed.

#[export] Instance entriesBlockDomainRangesInstance
    (returnAddress : Z) (args : EntriesToOwnedSliceBlockArgs) :
  ZesuDomainRanges (entriesBlockDomainAt returnAddress args) _ :=
  entriesBlockDomainRanges returnAddress args.
