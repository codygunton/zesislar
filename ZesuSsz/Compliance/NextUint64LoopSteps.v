Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Compliance.NextUint64FoldFacts.
Open Scope Z_scope.

Lemma nextUint64Header6318Step `{!islaG Sigma} `{!threadG}
    (params : NextUint64Args)
    (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : bv 64)
    (inputBytes sliceBytes decoded saved : list byte) :
  nextUint64EntryAt800d6318 params x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    inputBytes sliceBytes decoded saved ⊢
  ⌜(nextUint64DecodedLength decoded <> 0 /\
    (forall nextByte : byte,
      nth_error (nextUint64Payload (nextUint64Base params) decoded)
        (Z.to_nat (bv_unsigned x12 - nextUint64DecodedPointer decoded)) = Some nextByte ->
      (bv_unsigned x12 + 1 < bv_unsigned x13 ->
       nextUint64FoldInvariant (nextUint64Base params) decoded
         (Z_to_bv 64 (bv_unsigned x12 + 1)) x13
         (Z_to_bv 64 (bv_unsigned x11 * 256 + bv_unsigned nextByte))) /\
      (bv_unsigned x12 + 1 = bv_unsigned x13 ->
       nextUint64FoldComplete (nextUint64Base params) decoded
         (Z_to_bv 64 (bv_unsigned x11 * 256 + bv_unsigned nextByte)))))%Z⌝.
Proof.
unfold nextUint64EntryAt800d6318.
iIntros "Hentry".
iDestruct "Hentry" as "(_ & _ & _ & _ & %Hfacts & _)".
destruct Hfacts as (Hpost & Hinput & Hslice & Hinv & Hconsumed).
iPureIntro. split.
{ destruct Hinv as (cursor & Hcurrent & Haccepted & Hnonzero & Hrest).
  exact Hnonzero. }
{ intros nextByte Hbyte. split.
  { intro Hguard.
    exact (nextUint64FoldStep (nextUint64Base params) decoded x12 x13 x11
      nextByte Hinv Hbyte Hguard). }
  { intro Hguard.
    exact (nextUint64FoldLast (nextUint64Base params) decoded x12 x13 x11
      nextByte Hinv Hbyte Hguard). } }
Qed.
