Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
From Coq Require Import ZArith.ZArith Lia.
From stdpp Require Import bitvector.definitions.
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

(* The function-entry statement's return-address conjunct: the Level-1
   layout keeps the return address in range and 4-aligned. *)
Lemma nextUint64BoundaryDomainReturnAlignment (params : NextUint64Args) :
  nextUint64BoundaryDomain params ->
  (bv_unsigned (Z_to_bv 64 (nextReturnAddress (nextUint64Base params))) mod 4 = 0)%Z.
Proof.
  unfold nextUint64BoundaryDomain, nextUint64EntryLayout; cbv zeta.
  intros domain. repeat match goal with H : _ /\ _ |- _ => destruct H end.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
  assumption.
Qed.
