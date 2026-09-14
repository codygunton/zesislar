Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsOwnership.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma access_storage_ownership_return `{!islaG Sigma}
    entries processed entry rest :
  (bv_unsigned (writeSuccessAccessEntryStoragePointer entry) ↦ₘ∗
      writeSuccessAccessEntryStorageBytes entry ∗
   writeSuccessAccessEntriesOwn processed ∗ writeSuccessAccessEntriesOwn rest ∗
   ⌜writeSuccessAccessEntryValid entry⌝ ∗
   ⌜writeSuccessAccessEntryStorageCount entry <> 0%nat ->
     (mapRamBase defaultMap) <= bv_unsigned (writeSuccessAccessEntryStoragePointer entry)⌝ ∗
   ⌜writeSuccessAccessEntryStorageCount entry <> 0%nat ->
     bv_unsigned (writeSuccessAccessEntryStoragePointer entry) +
       Z.of_nat (length (writeSuccessAccessEntryStorageBytes entry)) < (machineRamEnd defaultMap)⌝ ∗
   ⌜entries = processed ++ entry :: rest⌝ ∗ True)%I -∗
  writeSuccessAccessEntriesOwn entries.
Proof.
  iIntros "(Hkeys & Hprocessed & Hrest & %Hvalid & %Hlow & %Hhigh & %Hpartition & _)".
  iAssert (writeSuccessAccessEntryOwn entry) with "[Hkeys]" as "Hentry".
  { unfold writeSuccessAccessEntryOwn. iSplitL "Hkeys"; last done.
    unfold writeSuccessAccessEntryStorageOwn.
    destruct (writeSuccessAccessEntryStorageCount entry) as [|n] eqn:Hcount; first done.
    iFrame. iSplit; last (iSplit; last done).
    - iPureIntro. apply Hlow. discriminate.
    - iPureIntro. apply Hhigh. discriminate. }
  rewrite Hpartition access_entries_own_app.
  cbn [writeSuccessAccessEntriesOwn]. iFrame; done.
Qed.
Print Assumptions access_storage_ownership_return.
