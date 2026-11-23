From Coq Require Import ZArith Lia.
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
  toOwnedReturnAddress (keysBase args) = returnAddress /\
  0 <= returnAddress < 2 ^ 64 /\
  0 <= arrayListLength (keysBlockList args) <= 2 ^ 24 /\
  0 <= arrayListCapacity (keysBlockList args) <= 2 ^ 24 /\
  arrayListLength (keysBlockList args) <= arrayListCapacity (keysBlockList args) /\
  1 <= arrayListPointer (keysBlockList args) < 2 ^ 64 /\
  Z.of_nat (length (arrayListItems (keysBlockList args))) =
    arrayListLength (keysBlockList args) * keysElementBytes /\
  toOwnedSliceDomain keysElementBytes (keysBase args) /\
  keysBlockRamLow <= toOwnedResultPointer (keysBase args) /\
  toOwnedResultPointer (keysBase args) + keysBlockResultBytes <= keysBlockRamHigh /\
  keysBlockRamLow <= toOwnedListPointer (keysBase args) /\
  toOwnedListPointer (keysBase args) + keysBlockHeaderBytes <= keysBlockRamHigh /\
  keysBlockRamLow <= toOwnedAllocatorPointer (keysBase args) /\
  toOwnedAllocatorPointer (keysBase args) + keysBlockAllocatorBytes <= keysBlockRamHigh /\
  keysBlockRamLow + keysBlockFrameBytes + keysBlockCalleeBytes <=
    toOwnedStackPointer (keysBase args) <= keysBlockRamHigh.
Proof.
  unfold keysBlockDomainAt, keysBlockArgsWellFormed.
  intros [<- H]. intuition lia.
Qed.

#[export] Instance keysBlockDomainRangesInstance
    (returnAddress : Z) (args : KeysToOwnedSliceBlockArgs) :
  ZesuDomainRanges (keysBlockDomainAt returnAddress args) _ :=
  keysBlockDomainRanges returnAddress args.
