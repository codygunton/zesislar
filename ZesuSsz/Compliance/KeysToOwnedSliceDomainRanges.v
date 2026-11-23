From Coq Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import ZesuSsz.Automation2.DomainRanges.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Open Scope Z_scope.

(* The ranges and links of the folded keysToOwnedSlice block domain as plain
   facts (DomainRanges.v). The alignment facts stay folded: a symbolic `mod`
   in the context makes every failing `lia` search branch on its quotient.
   `toOwnedSliceDomain` is posed as a fact so that its own instance
   (ArrayListContract.v) adds its ranges. *)
Lemma keysBlockDomainRanges (returnAddress : Z) (args : KeysToOwnedSliceBlockArgs) :
  keysBlockDomainAt returnAddress args ->
  bv_unsigned (keysReturnAddress args) = returnAddress /\
  0 <= returnAddress < 2 ^ 64 /\
  0 <= arrayListLength (keysBlockList args) <= 2 ^ 24 /\
  0 <= arrayListCapacity (keysBlockList args) <= 2 ^ 24 /\
  arrayListLength (keysBlockList args) <= arrayListCapacity (keysBlockList args) /\
  1 <= arrayListPointer (keysBlockList args) < 2 ^ 64 /\
  Z.of_nat (length (arrayListItems (keysBlockList args))) =
    arrayListLength (keysBlockList args) * keysElementBytes /\
  toOwnedSliceDomain keysElementBytes (keysBase args) /\
  toOwnedReturnAddress (keysBase args) = bv_unsigned (keysReturnAddress args) /\
  toOwnedStackPointer (keysBase args) = bv_unsigned (keysStackPointer args) /\
  toOwnedResultPointer (keysBase args) = bv_unsigned (keysResultPointer args) /\
  toOwnedListPointer (keysBase args) = bv_unsigned (keysListPointer args) /\
  toOwnedAllocatorPointer (keysBase args) = bv_unsigned (keysAllocatorPointer args) /\
  keysBlockRamLow <= bv_unsigned (keysResultPointer args) /\
  bv_unsigned (keysResultPointer args) + keysBlockResultBytes <= keysBlockRamHigh /\
  keysBlockRamLow <= bv_unsigned (keysListPointer args) /\
  bv_unsigned (keysListPointer args) + keysBlockHeaderBytes <= keysBlockRamHigh /\
  keysBlockRamLow <= bv_unsigned (keysAllocatorPointer args) /\
  bv_unsigned (keysAllocatorPointer args) + keysBlockAllocatorBytes <= keysBlockRamHigh /\
  keysBlockRamLow + keysBlockFrameBytes + keysBlockCalleeBytes <=
    bv_unsigned (keysStackPointer args) <= keysBlockRamHigh.
Proof.
  unfold keysBlockDomainAt, keysBlockArgsWellFormed.
  intros [<- H].
  pose proof (bv_unsigned_in_range _ (keysReturnAddress args)) as Hrange.
  change (bv_modulus 64) with (2 ^ 64) in Hrange.
  intuition lia.
Qed.

#[export] Instance keysBlockDomainRangesInstance
    (returnAddress : Z) (args : KeysToOwnedSliceBlockArgs) :
  ZesuDomainRanges (keysBlockDomainAt returnAddress args) _ :=
  keysBlockDomainRanges returnAddress args.
