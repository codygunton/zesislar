From Coq Require Import List ZArith.ZArith Lia.
From stdpp Require Import base list bitvector.definitions.
Require Import ZesuSsz.Automation2.CallSliceInterface.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Interfaces.NextUint64.
Import ListNotations.
Local Open Scope Z_scope.

(* nextUint64 as the callee of decodeParentHeader through the by-reference
   call step (`Automation2/CallSlice.v`, `ZesuCallSliceRefCaller`): a call on
   any window of decodeParentHeader's input, with the slice record and the
   16-byte output slot at two disjoint places of the 400-byte frame and the
   callee's stack pointer at the frame's base, satisfies nextUint64's
   domain. *)
Lemma parentHeaderNextUint64CallDomain (args : ParentHeaderArgs) (out ref p l sp : bv 64)
    (k j : Z) (rest : list (bv 64)) :
  parentHeaderArgsWellFormed args ->
  (bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned p /\
   bv_unsigned p + bv_unsigned l <= bv_unsigned (parentHeaderInputPointer args) +
     Z.of_nat (length (parentHeaderInputBytes args))) ->
  bv_unsigned sp = bv_unsigned (parentHeaderStackPointer args) - 400 ->
  bv_unsigned out = bv_unsigned (parentHeaderStackPointer args) - 400 + k -> 0 <= k <= 384 ->
  bv_unsigned ref = bv_unsigned (parentHeaderStackPointer args) - 400 + j -> 0 <= j <= 384 ->
  (k + 16 <= j \/ j + 16 <= k) ->
  nextUint64CallDomain (nextUint64CallDataArgs (out :: ref :: rest) sp p
    (parentHeaderInputEnd args)
    (take (Z.to_nat (bv_unsigned l))
      (drop (Z.to_nat (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args)))
        (parentHeaderInputBytes args)))).
Proof.
  intros Hwf [Hlo Hhi] Hsp Hout Hk Href Hj Hsep.
  apply nextUint64CallDomainIntro.
  pose proof (bv_unsigned_in_range _ l) as Hl.
  pose proof (bv_unsigned_in_range _ p) as Hp.
  pose proof (bv_unsigned_in_range _ (parentHeaderInputEnd args)) as He.
  assert (Hlen : Z.of_nat (length (take (Z.to_nat (bv_unsigned l))
    (drop (Z.to_nat (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args)))
      (parentHeaderInputBytes args)))) = bv_unsigned l)
    by (rewrite length_take, length_drop; lia).
  unfold parentHeaderArgsWellFormed, separateRanges in Hwf.
  unfold nextUint64BoundaryDomain, nextUint64EntryLayout, decodeItemEntryLayout, separateRanges,
    nextUint64CallDataArgs.
  cbn [nextUint64Base nextUint64InputEnd nextInputPointer nextInputBytes nextSlicePointer
       nextResultPointer nextStackPointer nextReturnAddress].
  change ((out :: ref :: rest) !!! 1%nat) with ref.
  change ((out :: ref :: rest) !!! 0%nat) with out.
  rewrite Hlen, Hsp, Hout, Href.
  cbv [Machine.mapRamBase Machine.mapRamSize Machine.machineRamEnd Machine.defaultMap] in *.
  change (bv_modulus 64) with 18446744073709551616 in *.
  change (2 ^ 64) with 18446744073709551616 in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; try lia.
  all: cbv [Machine.mapInputBufferAddress Machine.mapInputCapacity] in *.
  all: try lia.
  all: apply Z.mod_divide; [lia|].
  all: rewrite Zminus_mod;
    match goal with H : _ mod 16 = 0 |- _ =>
      rewrite H end; reflexivity.
Qed.

#[export] Instance parentHeaderNextUint64CallSlice :
  ZesuCallSliceRefCaller parentHeaderArgsWellFormed nextUint64CallDomain nextUint64CallDataArgs
    (fun args => bv_unsigned (parentHeaderInputPointer args))
    (fun args => parentHeaderInputBytes args)
    (fun args => bv_unsigned (parentHeaderStackPointer args) - 400)
    (fun args => parentHeaderInputEnd args)
    384 16.
Proof.
  intros args out ref p l sp k j rest Hwf Hwin Hsp Hout Hk Href Hj Hsep.
  exact (parentHeaderNextUint64CallDomain args out ref p l sp k j rest
    Hwf Hwin Hsp Hout Hk Href Hj Hsep).
Qed.
