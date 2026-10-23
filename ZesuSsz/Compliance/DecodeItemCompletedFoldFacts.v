Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Export ZesuSsz.Compliance.DecodeItemFoldExitFacts.
From Coq Require Import Lia.
Open Scope Z_scope.

Lemma decodeItemCompletedFoldFacts args n i payloadStart bytes :
  decodeItemByteFoldFacts args n i payloadStart bytes ->
  decodeItemByteFoldFacts args n n payloadStart bytes.
Proof.
  unfold decodeItemByteFoldFacts. intros (Hwidth & Hi & Hstart & Hbytes & Hlength & Hfits).
  repeat split; try assumption; lia.
Qed.

Print Assumptions decodeItemCompletedFoldFacts.
