From Coq Require Import List ZArith.ZArith Lia.
From stdpp Require Import base list bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Automation2.CallSliceInterface.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemCallData.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Export ZesuSsz.Contracts.DecodeItemCallSlice.
Import ListNotations.
Local Open Scope Z_scope.

(* decodeParentHeader may call decodeItem on any window of its input with any
   40-byte output slot of its own 400-byte frame. *)
Lemma parentHeaderDecodeItemCallDomain (args : ParentHeaderArgs) (p l out sp : bv 64) (k : Z)
    (rest : list (bv 64)) (before : list byte) :
  parentHeaderArgsWellFormed args ->
  (bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned p /\
   bv_unsigned p + bv_unsigned l <= bv_unsigned (parentHeaderInputPointer args) +
     Z.of_nat (length (parentHeaderInputBytes args))) ->
  bv_unsigned sp = bv_unsigned (parentHeaderStackPointer args) - 400 ->
  bv_unsigned out = bv_unsigned (parentHeaderStackPointer args) - 400 + k ->
  0 <= k <= 360 ->
  length before = 40%nat ->
  decodeItemCallDomain (decodeItemCallDataArgs (out :: p :: l :: rest)
    sp (bv_unsigned (parentHeaderInputEnd args))
    (take (Z.to_nat (bv_unsigned l))
      (drop (Z.to_nat (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args)))
        (parentHeaderInputBytes args)))
    before).
Proof.
  intros Hwf [Hlo Hhi] Hsp Hout Hk Hbefore.
  apply decodeItemCallDomainIntro.
  unfold decodeItemC1BDomain, decodeItemArgsWellFormed, decodeItemEntryLayout, separateRanges,
    decodeItemCallDataArgs.
  cbn.
  unfold parentHeaderArgsWellFormed, separateRanges in Hwf.
  rewrite length_take, length_drop, Hsp, Hout.
  pose proof (bv_unsigned_in_range _ l) as Hl.
  pose proof (bv_unsigned_in_range _ p) as Hp.
  pose proof (bv_unsigned_in_range _ (parentHeaderInputEnd args)) as He.
  change (bv_modulus 64) with 18446744073709551616 in *.
  change (2 ^ 64) with 18446744073709551616.
  destruct Hwf as (Hlen & _ & _ & _ & _ & Hwf).
  repeat split; first [exact Hbefore | lia].
Qed.

#[export] Instance parentHeaderDecodeItemCallSlice :
  ZesuCallSliceCaller parentHeaderArgsWellFormed decodeItemCallSliceInterface
    (fun args => bv_unsigned (parentHeaderInputPointer args))
    (fun args => parentHeaderInputBytes args)
    (fun args => bv_unsigned (parentHeaderStackPointer args) - 400)
    (fun args => bv_unsigned (parentHeaderInputEnd args))
    360.
Proof.
  intros args p l out sp k ie rest before Hwf Hwin Hsp Hout Hk -> Hbefore.
  exact (parentHeaderDecodeItemCallDomain args p l out sp k rest before
    Hwf Hwin Hsp Hout Hk Hbefore).
Qed.
