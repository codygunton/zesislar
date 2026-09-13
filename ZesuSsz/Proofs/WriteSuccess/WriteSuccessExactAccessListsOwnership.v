Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List.

Lemma access_entries_own_app `{!islaG Sigma} processed remaining :
  writeSuccessAccessEntriesOwn (processed ++ remaining) ⊣⊢
  (writeSuccessAccessEntriesOwn processed ∗ writeSuccessAccessEntriesOwn remaining ∗ True)%I.
Proof.
  induction processed as [|entry processed IH]; simpl.
  - iSplit.
    + iIntros "Hown". iFrame; done.
    + iIntros "(_ & Hown & _)". iExact "Hown".
  - rewrite IH. iSplit.
    + iIntros "(Hentry & (Hprocessed & Hremaining & _) & _)". iFrame; done.
    + iIntros "((Hentry & Hprocessed & _) & Hremaining & _)". iFrame; done.
Qed.
Print Assumptions access_entries_own_app.
