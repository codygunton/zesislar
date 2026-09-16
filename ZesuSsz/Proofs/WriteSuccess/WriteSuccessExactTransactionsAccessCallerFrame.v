Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsDataAccessEntry.

Lemma transactions_access_caller_frame `{!islaG Sigma} `{!threadG}
    sp x19 savedX22 count base entries bytes (F P : iProp Sigma) :
  (F ∗ transactionAccessAfterDataCaller sp x19 savedX22 count base entries bytes P)%I ⊣⊢
  transactionAccessAfterDataCaller sp x19 savedX22 count base entries bytes (F ∗ P ∗ True)%I.
Proof.
  rewrite /transactionAccessAfterDataCaller.
  iSplit.
  - iIntros "(HF & Hcaller)".
    iDestruct "Hcaller" as "(Hregs & H19 & Hsaved & Hbase & Hextra & Hkeys & Hbytes &
      Hentries & Hcount & Hencoding & Hlength & Hbound & Hstack & Hmin & Hmax & HP & _)".
    by iFrame.
  - iIntros "Hcaller".
    iDestruct "Hcaller" as "(Hregs & H19 & Hsaved & Hbase & Hextra & Hkeys & Hbytes &
      Hentries & Hcount & Hencoding & Hlength & Hbound & Hstack & Hmin & Hmax & (HF & HP & _) & _)".
    by iFrame.
Qed.
Print Assumptions transactions_access_caller_frame.
