Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
From Coq Require Import ZArith NArith Lia List.
Open Scope Z_scope.

Lemma s152_stageD_index32 (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) :
 length (returnStorage locals) = 40%nat ->
 (8%N = 8%N) /\
 exists i : nat,
 Z.of_nat i = Z.sub (Z.add (decodeItemOutputPointer args) 32) (decodeItemOutputPointer args) /\
 (i + N.to_nat 8 <= length (returnStorage locals))%nat.
Proof.
intros Hstorage. split; [reflexivity |]. exists 32%nat. split; [cbn; lia |]. rewrite Hstorage. cbn. lia.
Qed.
