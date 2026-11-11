Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.DecodeItemFrameImage.
Require Import ZesuSsz.Contracts.DecodeItemPayloadBounds.
From Coq Require Import List ZArith.ZArith Lia.
From stdpp Require Import list_numbers bitvector.definitions.
Open Scope Z_scope.

(* The Z ranges of nextUint64's domain quantities, as separate derived facts
   of the folded domain (the decodeItem mechanism, DecodeItemDomainRanges.v).
   A block proof saturates them; the domain predicate stays folded. *)
Lemma nextUint64BoundaryDomainRanges (params : NextUint64Args) :
  nextUint64BoundaryDomain params ->
  112 <= nextStackPointer (nextUint64Base params) < bv_modulus 64 /\
  0 <= nextInputPointer (nextUint64Base params) < bv_modulus 64 /\
  0 <= Z.of_nat (length (nextInputBytes (nextUint64Base params))) < bv_modulus 64 /\
  0 <= nextSlicePointer (nextUint64Base params) < bv_modulus 64 /\
  0 <= nextResultPointer (nextUint64Base params) < bv_modulus 64 /\
  0 <= nextReturnAddress (nextUint64Base params) < bv_modulus 64 /\
  0 <= nextUint64InputEnd params < bv_modulus 64.
Proof.
  unfold nextUint64BoundaryDomain, nextUint64EntryLayout, bv_modulus; cbv zeta.
  intros domain.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  change (2 ^ Z.of_N 64) with (2 ^ 64).
  repeat split; lia.
Qed.

#[export] Instance nextUint64BoundaryDomainStackPointerRangeDerivedFacts (params : NextUint64Args) :
  ZesuDerivedFacts (nextUint64BoundaryDomain params)
    (112 <= nextStackPointer (nextUint64Base params) < bv_modulus 64%N)%Z.
Proof. intro domain. pose proof (nextUint64BoundaryDomainRanges params domain). tauto. Qed.

#[export] Instance nextUint64BoundaryDomainInputPointerRangeDerivedFacts (params : NextUint64Args) :
  ZesuDerivedFacts (nextUint64BoundaryDomain params)
    (0 <= nextInputPointer (nextUint64Base params) < bv_modulus 64%N)%Z.
Proof. intro domain. pose proof (nextUint64BoundaryDomainRanges params domain). tauto. Qed.

#[export] Instance nextUint64BoundaryDomainInputLengthRangeDerivedFacts (params : NextUint64Args) :
  ZesuDerivedFacts (nextUint64BoundaryDomain params)
    (0 <= Z.of_nat (length (nextInputBytes (nextUint64Base params))) < bv_modulus 64%N)%Z.
Proof. intro domain. pose proof (nextUint64BoundaryDomainRanges params domain). tauto. Qed.

#[export] Instance nextUint64BoundaryDomainSlicePointerRangeDerivedFacts (params : NextUint64Args) :
  ZesuDerivedFacts (nextUint64BoundaryDomain params)
    (0 <= nextSlicePointer (nextUint64Base params) < bv_modulus 64%N)%Z.
Proof. intro domain. pose proof (nextUint64BoundaryDomainRanges params domain). tauto. Qed.

#[export] Instance nextUint64BoundaryDomainResultPointerRangeDerivedFacts (params : NextUint64Args) :
  ZesuDerivedFacts (nextUint64BoundaryDomain params)
    (0 <= nextResultPointer (nextUint64Base params) < bv_modulus 64%N)%Z.
Proof. intro domain. pose proof (nextUint64BoundaryDomainRanges params domain). tauto. Qed.

#[export] Instance nextUint64BoundaryDomainReturnAddressRangeDerivedFacts (params : NextUint64Args) :
  ZesuDerivedFacts (nextUint64BoundaryDomain params)
    (0 <= nextReturnAddress (nextUint64Base params) < bv_modulus 64%N)%Z.
Proof. intro domain. pose proof (nextUint64BoundaryDomainRanges params domain). tauto. Qed.

#[export] Instance nextUint64BoundaryDomainInputEndRangeDerivedFacts (params : NextUint64Args) :
  ZesuDerivedFacts (nextUint64BoundaryDomain params)
    (0 <= nextUint64InputEnd params < bv_modulus 64%N)%Z.
Proof. intro domain. pose proof (nextUint64BoundaryDomainRanges params domain). tauto. Qed.

Lemma nextUint64Word64BytesEncoding (value : Z) :
  bv_to_little_endian 8 8 value = word64Bytes value.
Proof.
  unfold word64Bytes, bv_to_little_endian, Z_to_little_endian.
  cbn [List.seq List.map Z.iter]. cbn.
  rewrite !Z.shiftr_shiftr; try lia.
  cbn. rewrite Z.shiftr_0_r. rewrite !Z.land_ones; try lia.
  repeat apply f_equal2; try reflexivity; apply bv_eq;
    rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn;
    rewrite Z.mod_mod; try reflexivity; lia.
Qed.

(* decodeItem's argument 1 is the word loaded from the slice's first 8 bytes:
   the input pointer. *)
Lemma nextUint64SliceImageWord0 (pointer count : Z) :
  0 <= pointer < 2 ^ 64 ->
  bv_unsigned (listWord64At0 (nextUint64SliceImage pointer count)) = pointer.
Proof.
  intros Hpointer. apply listWord64At0Value. unfold word64At, nextUint64SliceImage.
  rewrite <- !nextUint64Word64BytesEncoding. cbn [skipn].
  assert (Hlength : length (bv_to_little_endian 8 8 pointer) = 8%nat)
    by (rewrite length_bv_to_little_endian by lia; reflexivity).
  rewrite firstn_app, Hlength, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite firstn_all2 by (rewrite length_bv_to_little_endian by lia; cbn; lia).
  split; [exact Hlength|].
  apply (littleEndian_machine_bytes 8). exact Hpointer.
Qed.

#[export] Instance nextUint64BoundaryDomainSliceWord0DerivedFacts (params : NextUint64Args) :
  ZesuDerivedFacts (nextUint64BoundaryDomain params)
    (bv_unsigned (listWord64At0 (nextUint64SliceImage (nextInputPointer (nextUint64Base params))
       (Z.of_nat (length (nextInputBytes (nextUint64Base params)))))) =
     nextInputPointer (nextUint64Base params)).
Proof.
  intro domain. apply nextUint64SliceImageWord0.
  pose proof (nextUint64BoundaryDomainRanges params domain) as ranges.
  unfold bv_modulus in ranges. change (2 ^ Z.of_N 64) with (2 ^ 64) in ranges. tauto.
Qed.
