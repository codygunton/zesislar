Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactBlobHashesAuthorizationEntry
  WriteSuccessExactTransactionsSourceFieldLayout
  WriteSuccessExactTransactionsSourceBlobFeeFrame.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSourceSignatureLoanSpec
  WriteSuccessExactTransactionsSourceSignatureLoanFactor.

Lemma transactions_source_signature_memory `{!islaG Sigma} `{!threadG}
    sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes (Q : iProp Sigma) :
  transactionSourceBlobFeeRetained sp base bytes processed index dataBytes accessBytes
    chainBytes entries blobBytes Q -∗
  reg_col [(KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)] ∗
  transactionSourceSignatureWords sp bytes index ∗ (bv_unsigned sp - 48) ↦ₘ? 16 ∗
  transactionSourceSignatureLoan sp base bytes processed index dataBytes accessBytes
    chainBytes entries blobBytes Q.
Proof.
  iIntros "Hframe".
  iEval (rewrite transactions_source_signature_factor) in "Hframe".
  iDestruct "Hframe" as "(Hregs & Hwords & Hlower & Hremaining)".
  iSplitL "Hregs"; first iExact "Hregs".
  iSplitL "Hwords"; first iExact "Hwords".
  iSplitL "Hlower"; first iExact "Hlower".
  unfold transactionSourceSignatureLoan. iIntros "Hregs Hwords Hlower".
  iEval (rewrite transactions_source_signature_factor). iFrame.
Qed.
Print Assumptions transactions_source_signature_memory.
