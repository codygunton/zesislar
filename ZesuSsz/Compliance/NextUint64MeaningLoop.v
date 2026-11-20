(* The loop body of nextUint64 (entry 0x00a4) in the machine's spelling:
   one shift-or step keeps the fold invariant, the last step completes the
   fold. Split from NextUint64Meaning because NextUint64FoldFacts loads the
   legacy automation, which block callers must not load. *)
From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Compliance.NextUint64FoldFacts.
Require Import ZesuSsz.Compliance.NextUint64Meaning.
Open Scope Z_scope.

(* Loop steps of entry 0x00a4 in the machine's spelling. Premise [invariant]
   must be supplied by the generated entry 0x00a4. *)
Lemma nextUint64MachineFoldStep (args : NextUint64Call) (decoded : list byte)
    (current limit accumulator : bv 64) (nextByte : byte) :
  forall (Hinvariant : nextUint64FoldInvariant args decoded current limit accumulator),
  nth_error (nextUint64Payload args decoded)
    (Z.to_nat (bv_unsigned current - nextUint64DecodedPointer decoded)) = Some nextByte ->
  bv_unsigned current + 1 < bv_unsigned limit ->
  nextUint64FoldInvariant args decoded
    (Z_to_bv 64 (bv_unsigned current + 1)) limit
    (bv_or (bv_shiftl accumulator (BV 64 8)) (bv_zero_extend 64 nextByte)).
Proof.
  intros Hinvariant Hbyte Hguard. rewrite nextUint64ShiftOrStep.
  exact (nextUint64FoldStep _ _ _ _ _ _ Hinvariant Hbyte Hguard).
Qed.

Lemma nextUint64MachineFoldLast (args : NextUint64Call) (decoded : list byte)
    (current limit accumulator : bv 64) (nextByte : byte) :
  forall (Hinvariant : nextUint64FoldInvariant args decoded current limit accumulator),
  nth_error (nextUint64Payload args decoded)
    (Z.to_nat (bv_unsigned current - nextUint64DecodedPointer decoded)) = Some nextByte ->
  bv_unsigned current + 1 = bv_unsigned limit ->
  nextUint64FoldComplete args decoded
    (bv_or (bv_shiftl accumulator (BV 64 8)) (bv_zero_extend 64 nextByte)).
Proof.
  intros Hinvariant Hbyte Hguard. rewrite nextUint64ShiftOrStep.
  exact (nextUint64FoldLast _ _ _ _ _ _ Hinvariant Hbyte Hguard).
Qed.
