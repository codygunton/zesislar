From Coq Require Import List ZArith.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.ParentHeaderLevel1.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderDomain.
Open Scope Z_scope.

(* The walk is a trigger for a known bug, not a public input domain. *)
Definition ReviewedNestedWrapTrigger : list byte -> Prop :=
  fun input =>
    exists pc remaining isList headerLength payloadLength,
      pc <> 0x800d5cf4 /\
      List.In pc
        (parentHeaderDecodeItemCallSites ++ parentHeaderNextUint64CallSites) /\
      candidateCallInputAt input pc remaining /\
      candidateDecodeItem remaining =
        candidateSuccess isList headerLength payloadLength /\
      binaryWrapCase headerLength payloadLength
        ((headerLength + payloadLength) mod word64Modulus).

Check (eq_refl : nestedWrapOccurs = ReviewedNestedWrapTrigger).
Check (eq_refl : nextUint64Domain = fun args =>
  nextUint64EntryLayout
    (nextInputPointer args) (Z.of_nat (List.length (nextInputBytes args)))
    (nextSlicePointer args) (nextResultPointer args)
    (nextStackPointer args) (nextReturnAddress args)).
Check (eq_refl : parentHeaderDomain = fun args =>
  parentHeaderEntryLayout
    (headerInputPointer args) (Z.of_nat (List.length (headerInputBytes args)))
    (headerResultPointer args) (headerStackPointer args)
    (headerReturnAddress args)).
