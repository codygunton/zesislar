Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.

Import ListNotations.

Lemma write_success_transactions_access_invariant_core
    `{!islaG Sigma} (entries : list writeSuccessAccessEntry)
    (bytes : list (bv 8)) (R : iProp Sigma)
    (Hbytes : bytes = writeSuccessAccessEntriesBytes entries)
    (Hlength : length bytes = (40 * length entries)%nat)
    (Hbound : (length entries < 2 ^ 64)%nat) :
  R -∗
  ⌜entries = [] ++ entries⌝ ∗
  ⌜bytes = writeSuccessAccessEntriesBytes entries⌝ ∗
  ⌜[] = writeSuccessAccessEntriesBytes []⌝ ∗
  ⌜bytes = writeSuccessAccessEntriesBytes entries⌝ ∗
  ⌜bytes = [] ++ bytes⌝ ∗
  ⌜length bytes = (40 * length entries)%nat⌝ ∗
  ⌜length ([] : list (bv 8)) = (40 * length ([] : list writeSuccessAccessEntry))%nat⌝ ∗
  ⌜length bytes = (40 * length entries)%nat⌝ ∗
  ⌜(length entries < 2 ^ 64)%nat⌝ ∗ R.
Proof.
  iIntros "HR".
  iSplit; [iPureIntro; reflexivity|].
  iSplit; [iPureIntro; exact Hbytes|].
  iSplit; [iPureIntro; reflexivity|].
  iSplit; [iPureIntro; exact Hbytes|].
  iSplit; [iPureIntro; reflexivity|].
  iSplit; [iPureIntro; exact Hlength|].
  iSplit; [iPureIntro; reflexivity|].
  iSplit; [iPureIntro; exact Hlength|].
  iSplit; [iPureIntro; exact Hbound|].
  iExact "HR".
Qed.
