Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
From Coq Require Import ZArith NArith Lia List.
Open Scope Z_scope.


Lemma s159_word_guard_equivalence (args : DecodeItemArgs) :
 (Z_to_bv 64 (decodeItemInputLength args) <> 0%bv) <->
 (bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0).
Proof.
split; [exact (decodeItemInputLengthWordNonzero args) | intros Hunsigned Hzero; apply Hunsigned; rewrite Hzero; reflexivity].
Qed.
