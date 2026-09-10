From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsStorageFrame.

Lemma write_success_access_lists_storage_frame_intro
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma)
    (sp : bv 64) (base : Z) (entry : writeSuccessAccessEntry)
    (entries processed remaining : list writeSuccessAccessEntry)
    (bytes prefix suffix : list (bv 8)) (savedX22 x10 x11 : bv 64)
    (tail : spec) (count : nat)
    (Hcount : writeSuccessAccessEntryStorageCount entry = S count)
    (Hvalid : writeSuccessAccessEntryValid entry)
    (HstorageLow :
      0x20000000 <= bv_unsigned (writeSuccessAccessEntryStoragePointer entry))
    (HstorageHigh :
      bv_unsigned (writeSuccessAccessEntryStoragePointer entry) +
        Z.of_nat (length (writeSuccessAccessEntryStorageBytes entry)) <
        0x40000000) :
  (base ↦ₘ∗ prefix ∗
   (base + 40 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
   writeSuccessAccessEntriesOwn processed ∗
   writeSuccessAccessEntriesOwn remaining ∗
   writeSuccessAccessListsCopiedScratch
     sp base (length entries) (length processed) entry savedX22 ∗ P ∗
   writeSuccessAccessListsInvariant sp base entries processed
     (entry :: remaining) bytes prefix suffix ∗
   instr_pre 0x153c0
     (writeSuccessAccessListsLoopExit
       sp base entries bytes tail x19 savedX22 P) ∗ True) -∗
  writeSuccessStorageKeysScratch sp ∗
  writeSuccessAccessListsStorageFrame x19 P sp
    (bv_unsigned (writeSuccessAccessEntryStoragePointer entry)) (S count)
    (writeSuccessAccessEntryStorageBytes entry)
    (writeSuccessAccessListsEvents sp remaining tail).
Proof.
  destruct Hvalid as
    [HentryLength [Hpointer [HcountWord [HstorageLength HcountBound]]]].
  iIntros "(Hprefix & Hsuffix & Hprocessed & Hremaining & Hcopied & HP &
    #Hinv & Hexit & _)".
  iDestruct "Hcopied" as
    "(Hsaved & Hbase & Htotal & Hindex & Hcopied & HoutputScratch &
      HstorageScratch & _)".
  iFrame "HstorageScratch".
  rewrite /writeSuccessAccessListsStorageFrame.
  iExists base, entry, entries, processed, remaining, bytes, prefix, suffix,
    x10, x11, savedX22, tail.
  iFrame "Hprefix Hsuffix Hprocessed Hremaining Hsaved Hbase Htotal Hindex
    Hcopied HoutputScratch HP Hinv Hexit".
  repeat iSplit; iPureIntro; try reflexivity; try assumption; try congruence.
Qed.
