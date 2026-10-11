Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
From Coq Require Import ZArith NArith Lia List.
Open Scope Z_scope.

Definition s159_left_2 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (prefix : byte) (rest : list byte) (n i payloadStart : Z) (lengthBytes : list byte) (next : byte) : Type :=
 ltac:(let T := type of (@decodeItemListSuccessorNamedCanonical Sigma _ _ args prefix rest n i payloadStart lengthBytes next) in exact T).
Definition s159_right_2 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (prefix : byte) (rest : list byte) (n i payloadStart : Z) (lengthBytes : list byte) (next : byte) : Type :=
 ltac:(let T := type of (@decodeItemListSuccessorExpandedCanonical Sigma _ _ args prefix rest n i payloadStart lengthBytes next) in exact T).

Lemma s159_conversion_2 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (prefix : byte) (rest : list byte) (n i payloadStart : Z) (lengthBytes : list byte) (next : byte) :
 @s159_left_2 Sigma _ _ args prefix rest n i payloadStart lengthBytes next = @s159_right_2 Sigma _ _ args prefix rest n i payloadStart lengthBytes next.
Proof.
reflexivity.
Qed.
