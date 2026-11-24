From Coq Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import ZesuSsz.Automation2.DomainRanges.
Require Export ZesuSsz.Contracts.ArrayListContract.
Require Export ZesuSsz.Contracts.KeysEnsureCapacityContract.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBlockEntries.
Open Scope Z_scope.

(* The ranges and links of the folded keysEnsureCapacity block domain as plain
   facts (DomainRanges.v). The alignment facts stay folded: a symbolic `mod`
   in the context makes every failing `lia` search branch on its quotient.
   `keysEnsureCapacityDomain` is posed as a fact so that its own instance
   (KeysEnsureCapacityContract.v) adds its ranges. *)
Lemma ensureBlockDomainRanges (returnAddress : Z) (args : KeysEnsureCapacityBlockArgs) :
  ensureBlockDomainAt returnAddress args ->
  bv_unsigned (ensureReturnAddress (ensureBase args)) = returnAddress /\
  0 <= returnAddress < 2 ^ 64 /\
  0 <= arrayListLength (ensureBlockList args) <= 2 ^ 24 /\
  0 <= arrayListCapacity (ensureBlockList args) <= 2 ^ 24 /\
  arrayListLength (ensureBlockList args) <= arrayListCapacity (ensureBlockList args) /\
  1 <= arrayListPointer (ensureBlockList args) < 2 ^ 64 /\
  Z.of_nat (length (arrayListItems (ensureBlockList args))) =
    arrayListLength (ensureBlockList args) * keysElementBytes /\
  0 <= bv_unsigned (ensureRequested (ensureBase args)) < ensureBlockMaxRequest /\
  keysEnsureCapacityDomain (ensureBase args) /\
  ensureBlockRamLow <= bv_unsigned (ensureListPointer (ensureBase args)) /\
  bv_unsigned (ensureListPointer (ensureBase args)) + ensureBlockHeaderBytes <=
    ensureBlockRamHigh /\
  ensureBlockRamLow <= bv_unsigned (ensureAllocatorPointer (ensureBase args)) /\
  bv_unsigned (ensureAllocatorPointer (ensureBase args)) + ensureBlockAllocatorBytes <=
    ensureBlockRamHigh /\
  ensureBlockRamLow + ensureBlockFrameBytes + ensureBlockCalleeBytes <=
    bv_unsigned (ensureStackPointer (ensureBase args)) <= ensureBlockRamHigh.
Proof.
  unfold ensureBlockDomainAt, ensureBlockArgsWellFormed.
  intros [<- H].
  pose proof (bv_unsigned_in_range _ (ensureReturnAddress (ensureBase args))) as Hrange.
  change (bv_modulus 64) with (2 ^ 64) in Hrange.
  intuition lia.
Qed.

#[export] Instance ensureBlockDomainRangesInstance
    (returnAddress : Z) (args : KeysEnsureCapacityBlockArgs) :
  ZesuDomainRanges (ensureBlockDomainAt returnAddress args) _ :=
  ensureBlockDomainRanges returnAddress args.
