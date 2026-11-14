From Coq Require Import List ZArith Lia.
From stdpp Require Import base list numbers bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemPayloadBounds.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderDomain.
Require Import ZesuSsz.Contracts.ParentHeaderContract.

Import ListNotations.
Open Scope Z_scope.

(* The exclusion is exact: for an input shorter than 2^64 - 9 bytes, the
   outer list wrap holds iff the first decodeItem call reports a list whose
   payload length is at least 2^64 - 9, the range that the call at
   0x800d5d34 would receive. *)
Lemma parentHeaderOuterListWrapExact (input : list byte) :
  Z.of_nat (length input) < 18446744073709551607 ->
  parentHeaderOuterListWrap input <->
  exists headerLength payloadLength,
    candidateDecodeItem input =
      candidateSuccess true headerLength payloadLength /\
    18446744073709551607 <= payloadLength.
Proof.
  intros Hlength. split.
  - intros (headerLength & payloadLength & Hc & Hh0 & Hp0 & Hwrap & _).
    exists headerLength, payloadLength. split; [exact Hc|].
    destruct (candidateDecodeItemSuccessBounds _ _ _ _ Hc) as (Hh & _ & _).
    change (2 ^ 64) with 18446744073709551616 in Hwrap. lia.
  - intros (headerLength & payloadLength & Hc & Hp).
    exists headerLength, payloadLength. split; [exact Hc|].
    destruct (candidateDecodeItemSuccessBounds _ _ _ _ Hc) as (Hh & Hfit & _).
    unfold binaryWrapCase. change (2 ^ 64) with 18446744073709551616 in *.
    destruct (Z_lt_le_dec (headerLength + payloadLength) 18446744073709551616)
      as [Hsmall | Hwrap].
    + rewrite Z.mod_small in Hfit by lia. lia.
    + repeat split; lia.
Qed.

(* Under the contract domain the first call's list payload is shorter than
   2^64 - 9 bytes, the premise of decodeItemPayloadInInput. *)
Lemma parentHeaderOuterPayloadBound (args : ParentHeaderArgs)
    headerLength payloadLength :
  parentHeaderArgsWellFormed args ->
  candidateDecodeItem (parentHeaderInputBytes args) =
    candidateSuccess true headerLength payloadLength ->
  payloadLength < 18446744073709551607.
Proof.
  intros Hwf Hc.
  assert (Hfree : ~ parentHeaderOuterListWrap (parentHeaderInputBytes args))
    by (unfold parentHeaderArgsWellFormed in Hwf; tauto).
  destruct Hwf as (Hlength & _ & _ & _ & _ & Hlow & Hhigh & _).
  assert (Hshort : Z.of_nat (length (parentHeaderInputBytes args)) <
    18446744073709551607) by lia.
  destruct (Z_lt_le_dec payloadLength 18446744073709551607) as [Hp | Hp];
    [exact Hp|].
  exfalso. apply Hfree. apply (parentHeaderOuterListWrapExact _ Hshort).
  exists headerLength, payloadLength. split; [exact Hc | exact Hp].
Qed.

(* The first call's C1-B result with the list flag set places its nonempty
   payload inside the input: decodeItemPayloadInInput applies. *)
Lemma parentHeaderOuterPayloadInInput (args : ParentHeaderArgs) before after :
  parentHeaderArgsWellFormed args ->
  C1BResult (bv_unsigned (parentHeaderInputPointer args))
    (parentHeaderInputBytes args) before after ->
  byteAt after 16 1 ->
  0 < bv_unsigned (listWord64At8 after) ->
  bv_unsigned (parentHeaderInputPointer args) <=
    bv_unsigned (listWord64At0 after) /\
  bv_unsigned (listWord64At0 after) + bv_unsigned (listWord64At8 after) <=
    bv_unsigned (parentHeaderInputPointer args) +
      Z.of_nat (length (parentHeaderInputBytes args)).
Proof.
  intros Hwf Hc1b Hlist Hpos.
  apply (decodeItemPayloadInInput _ _ before); [exact Hc1b | exact Hpos |].
  destruct Hc1b as (_ & Hresult & _).
  unfold candidateResult40 in Hresult.
  destruct (candidateDecodeItem (parentHeaderInputBytes args))
    as [|isList headerLength payloadLength] eqn:Hc.
  - rewrite (errorResult40Word8 after Hresult) in Hpos. lia.
  - destruct Hresult as (_ & _ & _ & H8 & H16 & _).
    apply listWord64At8Value in H8. rewrite H8.
    destruct isList.
    + exact (parentHeaderOuterPayloadBound args _ _ Hwf Hc).
    + unfold byteAt in Hlist, H16. rewrite H16 in Hlist. discriminate.
Qed.

(* Sanity. A list that wraps to consumed count 0 is excluded. *)
Lemma parentHeaderOuterListWrapWitness :
  parentHeaderOuterListWrap
    (List.map (Z_to_bv 8) [255; 255; 255; 255; 255; 255; 255; 255; 247]).
Proof.
  exists 9, (word64Modulus - 9).
  vm_compute; repeat split; congruence.
Qed.

(* The string wrap witness of decodeItem stays in the domain: the parent
   rejects it at the list check without another call. *)
Lemma parentHeaderOuterStringWrapInDomain :
  ~ parentHeaderOuterListWrap decodeItemWrapWitnessInput.
Proof. intros (headerLength & payloadLength & Hc & _). vm_compute in Hc. discriminate. Qed.

(* A fitting outer list with a nested wrap stays in the domain; the meaning
   names its nested wrap. *)
Lemma parentHeaderNestedWrapInDomain :
  nestedWrapOccurs fittingOuterHeader /\
  ~ parentHeaderOuterListWrap fittingOuterHeader.
Proof.
  split; [exact hostileNestedWrapOccurs|].
  intros (headerLength & payloadLength & Hc & _ & _ & Hwrap & _).
  vm_compute in Hc. injection Hc as <- <-.
  change (2 ^ 64) with 18446744073709551616 in Hwrap. lia.
Qed.
