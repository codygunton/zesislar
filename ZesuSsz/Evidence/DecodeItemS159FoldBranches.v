Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
From Coq Require Import ZArith NArith Lia List.
Open Scope Z_scope.


Lemma s159_fold_branches_disjoint (args : DecodeItemArgs) (prefix : byte) (rest : list byte)
 (n payloadStart : Z) (lengthBytes : list byte) :
 decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes ->
 decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes -> False.
Proof.
unfold decodeItemFoldProvenance. intros Hlist Hstring. cbn in Hlist,Hstring. lia.
Qed.
