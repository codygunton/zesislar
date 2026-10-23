Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.PureFactHints.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Compliance.DecodeItemBranchGuardFacts.
Require Import ZesuSsz.Compliance.DecodeItemHeaderWitnessFacts.
Require Import ZesuSsz.Compliance.DecodeItemFoldRejectionFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Compliance.DecodeItemSemanticIntroduction.
Require Import ZesuSsz.Compliance.DecodeItemSailIntroduction.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.





Lemma decodeItemOutputByte16Bound (storage : list byte) :
  length storage = 40%nat -> (16 < length storage)%nat.
Proof. intros Hlength. rewrite Hlength. lia. Qed.

Lemma decodeItemCompletedListFoldAlternateRejected args prefix rest n payloadStart bytes :
  decodeItemC1BDomain args ->
  decodeItemFoldProvenance args true prefix rest n payloadStart bytes ->
  decodeItemByteFoldFacts args n n payloadStart bytes ->
  ~ bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) >=
    bv_signed (bv_zero_extend 128
      (Z_to_bv 64 (bigEndian (take (Z.to_nat n) bytes)) + Z_to_bv 64 (n + 1))) ->
  decodeItemRejectedFacts args.
Proof.
  intros Hdomain Hprovenance Hfold Hguard.
  apply Znot_ge_lt in Hguard.
  eapply decodeItemCompletedFoldRejected; [exact Hdomain | exact Hprovenance | exact Hfold |].
  exact (decodeItemCompletedFoldRejectGuard args n payloadStart bytes Hfold Hguard).
Qed.






Print Assumptions decodeItemOutputByte16Bound.

Print Assumptions decodeItemCompletedListFoldAlternateRejected.
