Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
From Coq Require Import ZArith NArith Lia List.
Open Scope Z_scope.


Lemma s159_loaded_guards_disjoint (loaded : byte) :
 ~ (bv_signed (bv_sign_extend 128 (bv_sign_extend 64 loaded)) < bv_signed (0%bv : bv 128) /\
 ~ bv_signed (bv_sign_extend 128 (bv_sign_extend 64 loaded)) < bv_signed (0%bv : bv 128)).
Proof.
tauto.
Qed.
