From Coq Require Import List ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import ZesuSsz.Automation2.DomainRanges.
Require Import ZesuSsz.Contracts.TxAccessListContract.
Require Import ZesuSsz.Contracts.TxAccessListBlockEntries.
Open Scope Z_scope.

(* The links of the folded txAccessList block domain as plain facts
   (DomainRanges.v). `txAccessListArgsWellFormed` is posed as a fact so that
   its own instance (TxAccessListContract.v) adds its ranges. *)
Lemma txAccessListBlockDomainRanges (returnAddress : Z) (args : TxAccessListArgs) :
  txAccessListBlockDomainAt returnAddress args ->
  bv_unsigned (txReturnAddress args) = returnAddress /\
  0 <= returnAddress < 2 ^ 64 /\
  txAccessListArgsWellFormed args /\
  Z.of_nat (length (txInputBytes args)) = bv_unsigned (txInputLength args) /\
  Z.of_nat (length (txScratchBefore args)) = 8.
Proof.
  unfold txAccessListBlockDomainAt.
  intros [<- H].
  pose proof (bv_unsigned_in_range _ (txReturnAddress args)) as Hrange.
  change (bv_modulus 64) with (2 ^ 64) in Hrange.
  pose proof H as (_ & Hlength & _ & _ & Hscratch & _).
  repeat split; auto; lia.
Qed.

#[export] Instance txAccessListBlockDomainRangesInstance
    (returnAddress : Z) (args : TxAccessListArgs) :
  ZesuDomainRanges (txAccessListBlockDomainAt returnAddress args) _ :=
  txAccessListBlockDomainRanges returnAddress args.
