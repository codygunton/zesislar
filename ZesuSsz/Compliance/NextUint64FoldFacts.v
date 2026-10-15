Require Import ZesuSsz.Automation.All.
From Coq Require Import List ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Import ListNotations.
Open Scope Z_scope.

Lemma nextUint64BytesValueBound :
forall (bytes : list byte),
  (length bytes <= 8)%nat -> 0 <= bigEndian bytes < word64Modulus.
Proof.
intros bytes Hlength.
assert (Hrange : forall xs : list byte,
  0 <= bigEndian xs < 256 ^ Z.of_nat (length xs)).
{ intro xs. induction xs using rev_ind.
  - cbn [bigEndian fold_left]. lia.
  - assert (Hsnoc : bigEndian (xs ++ [x]) = 256 * bigEndian xs + bv_unsigned x).
    { unfold bigEndian. rewrite fold_left_app. reflexivity. }
    rewrite Hsnoc.
    rewrite app_length.
    rewrite Nat2Z.inj_add. cbn [length Z.of_nat].
    rewrite Z.pow_add_r by lia.
    pose proof (bv_unsigned_in_range 8 x) as Hbyte.
    change (0 <= bv_unsigned x < 256) in Hbyte.
    cbn [Z.pow]. nia. }
pose proof (Hrange bytes) as Hvalue.
assert (Hpower : 256 ^ Z.of_nat (length bytes) <= 256 ^ 8).
{ apply Z.pow_le_mono_r; lia. }
change (0 <= bigEndian bytes < 18446744073709551616).
change (256 ^ Z.of_nat (length bytes) <= 18446744073709551616) in Hpower.
lia.
Qed.

Lemma nextUint64PrefixStepValue :
forall (bytes : list byte) (index : Z) (next : byte),
  0 <= index -> (length bytes <= 8)%nat ->
  nth_error bytes (Z.to_nat index) = Some next ->
  bv_unsigned (Z_to_bv 64
    (bigEndian (firstn (Z.to_nat index) bytes) * 256 + bv_unsigned next)) =
  bigEndian (firstn (Z.to_nat (index + 1)) bytes).
Proof.
intros bytes index next Hindex Hlength Hbyte.
assert (Hsnoc : firstn (Z.to_nat (index + 1)) bytes =
  firstn (Z.to_nat index) bytes ++ [next]).
{ replace (Z.to_nat (index + 1)) with (S (Z.to_nat index)) by lia.
  destruct (@nth_error_split byte bytes (Z.to_nat index) next Hbyte) as (left & right & Hlist & HleftLength).
  rewrite Hlist.
  assert (Hfirst : firstn (S (Z.to_nat index)) (left ++ next :: right) = left ++ [next]).
  { rewrite firstn_app. rewrite firstn_all2 by lia.
    replace (S (Z.to_nat index) - length left)%nat with 1%nat by lia.
    reflexivity. }
  assert (Hprevious : firstn (Z.to_nat index) (left ++ next :: right) = left).
  { rewrite firstn_app. rewrite firstn_all2 by lia.
    replace (Z.to_nat index - length left)%nat with 0%nat by lia.
    cbn [firstn]. apply app_nil_r. }
  rewrite Hfirst.
  rewrite Hprevious. reflexivity. }
assert (Hvalue : bigEndian (firstn (Z.to_nat (index + 1)) bytes) =
  bigEndian (firstn (Z.to_nat index) bytes) * 256 + bv_unsigned next).
{ rewrite Hsnoc. unfold bigEndian. rewrite fold_left_app.
  cbn [fold_left]. rewrite (Z.mul_comm 256 _). reflexivity. }
assert (Hbound : 0 <= bigEndian (firstn (Z.to_nat (index + 1)) bytes) < bv_modulus 64).
{ change (0 <= bigEndian (firstn (Z.to_nat (index + 1)) bytes) < word64Modulus).
  apply nextUint64BytesValueBound.
  rewrite firstn_length. lia. }
rewrite <- Hvalue.
apply Z_to_bv_small. exact Hbound.
Qed.

Lemma nextUint64FoldInitialization :
forall (args : NextUint64Call) (decoded : list byte),
  nextUint64AcceptedBytes args decoded ->
  nextUint64DecodedLength decoded <> 0 ->
  0 <= nextUint64DecodedPointer decoded ->
  nextUint64DecodedPointer decoded + nextUint64DecodedLength decoded < word64Modulus ->
  Z.of_nat (length (nextUint64Payload args decoded)) = nextUint64DecodedLength decoded ->
  nextUint64FoldInvariant args decoded
    (Z_to_bv 64 (nextUint64DecodedPointer decoded))
    (Z_to_bv 64 (nextUint64DecodedPointer decoded + nextUint64DecodedLength decoded))
    (Z_to_bv 64 0).
Proof.
intros args decoded Haccepted Hnonzero Hpointer Hnowrap Hlength.
pose proof Haccepted as Hbounds.
destruct Hbounds as (header & payload & Hcandidate & Hheader & Hpayload & Hfit & Hsize & Hstart & HdecodedLength & Hconsumed & Hbytes).
assert (Hpositive : 0 < nextUint64DecodedLength decoded) by lia.
assert (HpointerBound : 0 <= nextUint64DecodedPointer decoded < bv_modulus 64).
{ change (0 <= nextUint64DecodedPointer decoded < word64Modulus). lia. }
assert (HendBound : 0 <= nextUint64DecodedPointer decoded + nextUint64DecodedLength decoded < bv_modulus 64).
{ change (0 <= nextUint64DecodedPointer decoded + nextUint64DecodedLength decoded < word64Modulus). lia. }
unfold nextUint64FoldInvariant.
exists (nextUint64DecodedPointer decoded).
rewrite (Z_to_bv_small 64 _ HpointerBound).
rewrite (Z_to_bv_small 64 _ HendBound).
replace (nextUint64DecodedPointer decoded - nextUint64DecodedPointer decoded) with 0 by lia.
cbn [Z.to_nat firstn bigEndian fold_left].
refine (conj eq_refl (conj Haccepted (conj Hnonzero _))).
repeat split; try assumption; try reflexivity; lia.
Qed.

Lemma nextUint64FoldStep :
forall (args : NextUint64Call) (decoded : list byte)
    (current limit accumulator : bv 64) (nextByte : byte),
  nextUint64FoldInvariant args decoded current limit accumulator ->
  nth_error (nextUint64Payload args decoded)
    (Z.to_nat (bv_unsigned current - nextUint64DecodedPointer decoded)) = Some nextByte ->
  bv_unsigned current + 1 < bv_unsigned limit ->
  nextUint64FoldInvariant args decoded
    (Z_to_bv 64 (bv_unsigned current + 1)) limit
    (Z_to_bv 64 (bv_unsigned accumulator * 256 + bv_unsigned nextByte)).
Proof.
intros args decoded current limit accumulator nextByte Hinv Hbyte Hguard.
unfold nextUint64FoldInvariant in Hinv.
destruct Hinv as (cursor & Hcurrent & Haccepted & Hnonzero & Hindex & Hlimit & Hpointer & Hnowrap & Hlength & Hacc).
pose proof Haccepted as Hbounds.
destruct Hbounds as (header & payload & Hcandidate & Hheader & Hpayload & Hfit & Hsize & Hstart & HdecodedLength & Hconsumed & Hbytes).
assert (Hwidth : (length (nextUint64Payload args decoded) <= 8)%nat) by lia.
rewrite Hcurrent in Hbyte.
rewrite Hcurrent in Hguard.
pose proof (nextUint64PrefixStepValue (nextUint64Payload args decoded)
  (cursor - nextUint64DecodedPointer decoded) nextByte ltac:(lia) Hwidth Hbyte) as Hstep.
rewrite <- Hacc in Hstep.
assert (HnextBound : 0 <= cursor + 1 < bv_modulus 64).
{ change (0 <= cursor + 1 < word64Modulus). lia. }
unfold nextUint64FoldInvariant.
exists (cursor + 1).
rewrite Hcurrent.
rewrite (Z_to_bv_small 64 _ HnextBound).
refine (conj eq_refl (conj Haccepted (conj Hnonzero _))).
split; first lia.
split; first exact Hlimit.
split; first exact Hpointer.
split; first exact Hnowrap.
split; first exact Hlength.
replace (cursor + 1 - nextUint64DecodedPointer decoded) with
  (cursor - nextUint64DecodedPointer decoded + 1) by lia.
exact Hstep.
Qed.

Lemma nextUint64FoldLast :
forall (args : NextUint64Call) (decoded : list byte)
    (current limit accumulator : bv 64) (nextByte : byte),
  nextUint64FoldInvariant args decoded current limit accumulator ->
  nth_error (nextUint64Payload args decoded)
    (Z.to_nat (bv_unsigned current - nextUint64DecodedPointer decoded)) = Some nextByte ->
  bv_unsigned current + 1 = bv_unsigned limit ->
  nextUint64FoldComplete args decoded
    (Z_to_bv 64 (bv_unsigned accumulator * 256 + bv_unsigned nextByte)).
Proof.
intros args decoded current limit accumulator nextByte Hinv Hbyte Hguard.
unfold nextUint64FoldInvariant in Hinv.
destruct Hinv as (cursor & Hcurrent & Haccepted & Hnonzero & Hindex & Hlimit & Hpointer & Hnowrap & Hlength & Hacc).
pose proof Haccepted as Hbounds.
destruct Hbounds as (header & payload & Hcandidate & Hheader & Hpayload & Hfit & Hsize & Hstart & HdecodedLength & Hconsumed & Hbytes).
assert (Hwidth : (length (nextUint64Payload args decoded) <= 8)%nat) by lia.
rewrite Hcurrent in Hbyte.
rewrite Hcurrent in Hguard.
pose proof (nextUint64PrefixStepValue (nextUint64Payload args decoded)
  (cursor - nextUint64DecodedPointer decoded) nextByte ltac:(lia) Hwidth Hbyte) as Hstep.
rewrite <- Hacc in Hstep.
unfold nextUint64FoldComplete.
split; first exact Haccepted.
rewrite Hstep.
assert (Hprocessed : cursor - nextUint64DecodedPointer decoded + 1 = nextUint64DecodedLength decoded) by lia.
rewrite Hprocessed.
replace (Z.to_nat (nextUint64DecodedLength decoded)) with
  (length (nextUint64Payload args decoded)) by lia.
rewrite firstn_all.
reflexivity.
Qed.

Lemma nextUint64EmptyFold :
forall (args : NextUint64Call) (decoded : list byte),
  nextUint64AcceptedBytes args decoded ->
  nextUint64DecodedLength decoded = 0 ->
  nextUint64FoldComplete args decoded (Z_to_bv 64 0).
Proof.
intros args decoded Haccepted Hzero.
unfold nextUint64FoldComplete.
split; first exact Haccepted.
unfold nextUint64Payload.
rewrite Hzero.
reflexivity.
Qed.

