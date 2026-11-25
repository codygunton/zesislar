From Coq Require Import List ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import ZesuSsz.Automation2.DomainRanges.
Require Import ZesuSsz.Contracts.TxAccessListContract.
Require Import ZesuSsz.Contracts.TxAccessListBlockEntries.
Open Scope Z_scope.

(* The links of the folded txAccessList block domain as plain facts
   (DomainRanges.v), with the frame's 16-byte and the allocator object's
   8-byte alignment (the array-list call domains state the slot alignments). `txAccessListArgsWellFormed` is posed as a fact so that
   its own instance (TxAccessListContract.v) adds its ranges. *)
Lemma txAccessListBlockDomainRanges (returnAddress : Z) (args : TxAccessListArgs) :
  txAccessListBlockDomainAt returnAddress args ->
  bv_unsigned (txReturnAddress args) = returnAddress /\
  0 <= returnAddress < 2 ^ 64 /\
  txAccessListArgsWellFormed args /\
  Z.of_nat (length (txInputBytes args)) = bv_unsigned (txInputLength args) /\
  Z.of_nat (length (txScratchBefore args)) = 8 /\
  bv_unsigned (txStackPointer args) mod 16 = 0 /\
  (8 | bv_unsigned (txAllocatorPointer args)).
Proof.
  unfold txAccessListBlockDomainAt.
  intros [<- H].
  pose proof (bv_unsigned_in_range _ (txReturnAddress args)) as Hrange.
  change (bv_modulus 64) with (2 ^ 64) in Hrange.
  pose proof H as (_ & _ & _ & _ & Halign & _).
  apply txAccessListBlockArgsWellFormed_contract in H.
  pose proof H as (_ & Hlength & Hsp & _ & Hscratch & _).
  split; [reflexivity|]. split; [lia|]. split; [exact H|]. split; [exact Hlength|].
  split; [exact Hscratch|]. split; [exact Hsp|exact Halign].
Qed.

#[export] Instance txAccessListBlockDomainRangesInstance
    (returnAddress : Z) (args : TxAccessListArgs) :
  ZesuDomainRanges (txAccessListBlockDomainAt returnAddress args) _ :=
  txAccessListBlockDomainRanges returnAddress args.
