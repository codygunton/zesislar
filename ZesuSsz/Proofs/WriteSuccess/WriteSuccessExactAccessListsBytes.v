Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List.

Lemma access_entries_bytes_app left right :
  writeSuccessAccessEntriesBytes (left ++ right) =
  writeSuccessAccessEntriesBytes left ++ writeSuccessAccessEntriesBytes right.
Proof. induction left; simpl; [reflexivity|rewrite IHleft app_assoc; reflexivity]. Qed.

Lemma access_entries_bytes_length entries :
  Forall writeSuccessAccessEntryValid entries ->
  length (writeSuccessAccessEntriesBytes entries) = (40 * length entries)%nat.
Proof.
  intros Hvalid. induction Hvalid as [|entry entries Hentry Hall IH]; simpl.
  - reflexivity.
  - rewrite app_length (proj1 Hentry) IH. lia.
Qed.

Lemma access_entries_bytes_slice processed entry remaining :
  Forall writeSuccessAccessEntryValid processed -> writeSuccessAccessEntryValid entry ->
  take 40 (drop (40 * length processed)
    (writeSuccessAccessEntriesBytes (processed ++ entry :: remaining))) =
  writeSuccessAccessEntryBytes entry.
Proof.
  intros Hprocessed Hentry. rewrite access_entries_bytes_app.
  rewrite <- (access_entries_bytes_length processed Hprocessed), drop_app_length.
  simpl. rewrite <- (proj1 Hentry), take_app_length. reflexivity.
Qed.

Print Assumptions access_entries_bytes_app.
Print Assumptions access_entries_bytes_length.
Print Assumptions access_entries_bytes_slice.
