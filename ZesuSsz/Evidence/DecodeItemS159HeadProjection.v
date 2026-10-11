Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
From Coq Require Import ZArith NArith Lia List.
Open Scope Z_scope.


Lemma s159_head_facts_projection (args : DecodeItemArgs) :
 (exists prefix rest, decodeItemInputHead args prefix rest /\
    bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0) ->
 exists prefix rest, decodeItemInputHead args prefix rest.
Proof.
intros [prefix [rest [Hhead Hnonzero]]]. exists prefix,rest. exact Hhead.
Qed.
