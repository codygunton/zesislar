Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsSourceFieldLayout.

Lemma transactions_source_blob_memory_frame `{!islaG Sigma}
    sp base bytes processed index dataBytes accessBytes pointer blobBytes (Q : iProp Sigma) :
  transactionFieldSourceRetained sp base bytes processed index dataBytes accessBytes
    (writeSuccessByteArrayOwn pointer blobBytes ∗ Q)%I -∗
  (bv_unsigned sp + 1680) ↦ₘ? 32 ∗ writeSuccessByteArrayOwn pointer blobBytes ∗
  ((bv_unsigned sp + 1680) ↦ₘ? 32 -∗
    transactionFieldSourceRetained sp base bytes processed index dataBytes accessBytes Q).
Proof.
  destruct blobBytes as [|byte blobBytes]; iStartProof; iIntros "Hmemory";
    iEval (unfold transactionFieldSourceRetained, writeSuccessByteArrayOwn) in "Hmemory";
    cbn; zesu_open_resource_groups;
    unfold transactionFieldSourceRetained, writeSuccessByteArrayOwn; cbn; zesu_run.
Qed.
Print Assumptions transactions_source_blob_memory_frame.
