Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List.

Lemma access_entries_validity `{!islaG Sigma} entries :
  writeSuccessAccessEntriesOwn entries -∗
  ⌜Forall writeSuccessAccessEntryValid entries⌝ ∗ writeSuccessAccessEntriesOwn entries.
Proof.
  induction entries as [|entry entries IH]; simpl.
  - iIntros "Hown". iFrame. iPureIntro. constructor.
  - iIntros "(Hentry & Hrest & _)".
    iDestruct "Hentry" as "(Hstorage & %Hvalid & _)".
    iDestruct (IH with "Hrest") as "[%Hall Hrest]".
    iSplit; first (iPureIntro; constructor; assumption).
    iFrame. iSplit; first done. done.
Qed.
Print Assumptions access_entries_validity.
