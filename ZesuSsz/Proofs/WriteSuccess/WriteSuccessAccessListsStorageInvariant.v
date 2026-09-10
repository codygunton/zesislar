From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopCommon.

Lemma write_success_access_lists_storage_invariant
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (entry : writeSuccessAccessEntry)
    (entries processed remaining : list writeSuccessAccessEntry)
    (bytes prefix suffix : list (bv 8)) (count : nat)
    (HstorageLength : length (writeSuccessAccessEntryStorageBytes entry) =
      (32 * S count)%nat)
    (HcountBound : (S count < 2 ^ 64)%nat)
    (HstorageLow :
      0x20000000 <= bv_unsigned (writeSuccessAccessEntryStoragePointer entry))
    (HstorageHigh :
      bv_unsigned (writeSuccessAccessEntryStoragePointer entry) +
        Z.of_nat (length (writeSuccessAccessEntryStorageBytes entry)) <
        0x40000000) :
  writeSuccessAccessListsInvariant sp base entries processed
    (entry :: remaining) bytes prefix suffix -∗
  writeSuccessFixedWidthArrayInvariant sp
    (writeSuccessAccessEntryStoragePointer entry)
    (bv_unsigned (writeSuccessAccessEntryStoragePointer entry))
    (S count) O count (writeSuccessAccessEntryStorageBytes entry).
Proof.
  iIntros "#Hinv".
  iDestruct "Hinv" as
    "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %Halign & %HspLow &
      %HspHigh & _)".
  rewrite /writeSuccessFixedWidthArrayInvariant.
  iSplit; [iPureIntro; reflexivity |].
  iSplit; [iPureIntro; exact HstorageLength |].
  iSplit; [iPureIntro; rewrite Z.mul_0_r Z.add_0_r; reflexivity |].
  iSplit; [iPureIntro; exact HcountBound |].
  iSplit; [iPureIntro; exact Halign |].
  iSplit; [iPureIntro;
    clear HcountBound HstorageLength HstorageLow HstorageHigh Halign HspHigh;
    lia |].
  iSplit; [iPureIntro; exact HspHigh |].
  iSplit; [iPureIntro; exact HstorageLow |].
  iSplit; [iPureIntro; exact HstorageHigh |].
  done.
Qed.
