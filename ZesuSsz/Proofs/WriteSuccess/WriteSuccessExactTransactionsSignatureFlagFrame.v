Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSignatureFieldEntry WriteSuccessExactTransactionsFieldFlagEntry.

Lemma transactions_signature_flag_frame `{!islaG Sigma} `{!threadG}
    sp row bytes index (P : iProp Sigma) :
  transactionSignatureFieldRetained sp row bytes index
    (reg_col [(KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗ P ∗ True)%I ⊣⊢
  transactionFieldFlagCaller bytes index
    (transactionSignatureFieldRetained sp row bytes index P).
Proof.
  iStartProof. rewrite /transactionSignatureFieldRetained /transactionFieldFlagCaller.
  iSplit.
  - iIntros "(H0 & H1 & H2 & %Halign & %Hlength & %Hhigh & (Hregs & HP & _) & _)".
    iFrame. repeat iSplit; try done; iPureIntro; lia.
  - iIntros "(Hregs & %HflagLength & (H0 & H1 & H2 & %Halign & %Hlength & %Hhigh & HP & _) & _)".
    iFrame. repeat iSplit; done.
Qed.
Print Assumptions transactions_signature_flag_frame.

