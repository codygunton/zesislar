Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
From Coq Require Import ZArith NArith Lia List.
Open Scope Z_scope.


Lemma s159_head_route_subsumption (returnAddress : Z) (args : DecodeItemArgs) :
 decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
 Z_to_bv 64 (decodeItemInputLength args) <> 0%bv ->
 exists prefix rest, decodeItemInputHead args prefix rest.
Proof.
intros Hdomain Hword.
apply (decodeItemInputHeadWitnessFacts returnAddress args Hdomain).
exact (decodeItemInputLengthWordNonzero args Hword).
Qed.
