Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsGasSignatureEntry WriteSuccessExactTransactionsSignatureFieldEntry.

Lemma transactions_gas_signature_retained_frame `{!islaG Sigma} `{!threadG}
    sp bytes index (F P : iProp Sigma) :
  transactionGasSignatureRetained sp bytes index (F ∗ P ∗ True)%I ⊣⊢
  (F ∗ transactionGasSignatureRetained sp bytes index P ∗ True)%I.
Proof.
  iStartProof. rewrite /transactionGasSignatureRetained.
  iSplit.
  - iIntros "(H25 & H24 & H9 & H23 & %Hlength & %Hhigh & (HF & HP & _) & _)".
    iFrame. repeat iSplit; done.
  - iIntros "(HF & (H25 & H24 & H9 & H23 & %Hlength & %Hhigh & HP & _) & _)".
    iFrame. repeat iSplit; done.
Qed.
Print Assumptions transactions_gas_signature_retained_frame.

Lemma transactions_gas_signature_caller_frame `{!islaG Sigma} `{!threadG}
    sp bytes index (P : iProp Sigma) :
  transactionGasSignatureRetained sp bytes index (transactionSignatureFieldCaller sp bytes index P) ⊣⊢
  transactionSignatureFieldCaller sp bytes index (transactionGasSignatureRetained sp bytes index P).
Proof.
  iStartProof. rewrite /transactionGasSignatureRetained /transactionSignatureFieldCaller.
  iSplit.
  - iIntros "(H25 & H24 & H9 & H23 & %Hlength & %Hhigh &
      (Hregs & Hscratch & %Hlength2 & %Hhigh2 & HP & _) & _)".
    iFrame. repeat iSplit; done.
  - iIntros "(Hregs & Hscratch & %Hlength2 & %Hhigh2 &
      (H25 & H24 & H9 & H23 & %Hlength & %Hhigh & HP & _) & _)".
    iFrame. repeat iSplit; done.
Qed.
Print Assumptions transactions_gas_signature_caller_frame.

