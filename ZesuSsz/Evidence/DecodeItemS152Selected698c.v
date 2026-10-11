Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
From Coq Require Import ZArith NArith Lia List.
Open Scope Z_scope.

Lemma s152_selected_698c_pure (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) :
 length (returnStorage locals) = 40%nat ->
 Z.modulo (Z.sub (Z.add (decodeItemOutputPointer args) 16) (decodeItemOutputPointer args)) 1 = 0 /\
 exists i : nat,
 Z.of_nat i = Z.div (Z.sub (Z.add (decodeItemOutputPointer args) 16) (decodeItemOutputPointer args)) 1 /\
 (i < length (returnStorage locals))%nat /\ (8%N = 8%N).
Proof.
intros Hstorage. split; [apply Z.mod_1_r |]. exists 16%nat. split; [rewrite Z.div_1_r; cbn; lia |]. split; [rewrite Hstorage; lia | reflexivity].
Qed.
