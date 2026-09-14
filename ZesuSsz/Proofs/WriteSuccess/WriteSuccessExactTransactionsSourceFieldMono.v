Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSourceFieldEvents WriteSuccessExactTransactionsSourceFieldLayout
  WriteSuccessExactTransactionsDataAccessEntry WriteSuccessExactAccessListsReturnCount
  WriteSuccessExactAccessListsReturnLoopEntry WriteSuccessExactEncoderIntFramedCall.

Lemma transactions_source_field_post_mono `{!islaG Sigma} `{!threadG}
    sp base bytes processed index dataBytes accessBytes chainBytes entries tail (P Q : iProp Sigma) :
  (P ⊢ Q) ->
  transactionSourceFieldPost sp base bytes processed index dataBytes accessBytes chainBytes entries tail P ⊢
  transactionSourceFieldPost sp base bytes processed index dataBytes accessBytes chainBytes entries tail Q.
Proof.
  intros Hmono.
  unfold transactionSourceFieldPost, accessReturnCountPost, encoderIntExactFramedPost,
    accessReturnCountFrame, accessReturnLoopFrame, accessReturnRuntimeBounds,
    transactionAccessRetainedMemory, transactionFieldSourceRetained.
  repeat first [apply bi.sep_mono | apply bi.exist_mono; intro].
  all: first [reflexivity | exact Hmono].
Qed.
Print Assumptions transactions_source_field_post_mono.
