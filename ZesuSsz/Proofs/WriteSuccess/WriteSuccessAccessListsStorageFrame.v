Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsBoundary15224.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.

Definition writeSuccessAccessListsStorageFrame
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma)
    (sp : bv 64) (storageBase : Z) (total : nat)
    (storageBytes : list (bv 8)) (tail : spec) :
    iProp Sigma :=
  (∃ (accessBase : Z) (entry : writeSuccessAccessEntry)
      (entries processed remaining : list writeSuccessAccessEntry)
      (bytes prefix suffix : list (bv 8)) (x10 x11 : bv 64)
      (savedX22 : bv 64) (finalTail : spec),
    accessBase ↦ₘ∗ prefix ∗
    (accessBase + 40 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
    writeSuccessAccessEntriesOwn processed ∗
    writeSuccessAccessEntriesOwn remaining ∗
    (bv_unsigned sp + 136) ↦ₘ savedX22 ∗
    (bv_unsigned sp + 256) ↦ₘ Z_to_bv 64 accessBase ∗
    (bv_unsigned sp + 264) ↦ₘ Z_to_bv 64 (Z.of_nat (length entries)) ∗
    (bv_unsigned sp + 272) ↦ₘ
      Z_to_bv 64 (Z.of_nat (length processed)) ∗
    (bv_unsigned sp + 1744) ↦ₘ∗ writeSuccessAccessEntryBytes entry ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    ⌜writeSuccessAccessEntryValid entry⌝ ∗
    ⌜storageBase =
      bv_unsigned (writeSuccessAccessEntryStoragePointer entry)⌝ ∗
    ⌜total = writeSuccessAccessEntryStorageCount entry⌝ ∗
    ⌜total <> 0%nat⌝ ∗
    ⌜storageBytes = writeSuccessAccessEntryStorageBytes entry⌝ ∗
    ⌜(mapRamBase defaultMap) <=
      bv_unsigned (writeSuccessAccessEntryStoragePointer entry)⌝ ∗
    ⌜bv_unsigned (writeSuccessAccessEntryStoragePointer entry) +
      Z.of_nat (length (writeSuccessAccessEntryStorageBytes entry)) <
      (machineRamEnd defaultMap)⌝ ∗
    ⌜tail = writeSuccessAccessListsEvents sp remaining finalTail⌝ ∗
    P ∗
    writeSuccessAccessListsInvariant sp accessBase entries processed
      (entry :: remaining) bytes prefix suffix ∗
    instr_pre 0x153c0
      (writeSuccessAccessListsLoopExit
        sp accessBase entries bytes finalTail x19 savedX22 P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessAccessListsStorageFrame) := I.

Definition writeSuccessAccessListsStorageAnyLoopSpec
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
    iProp Sigma :=
  (∃ (sp : bv 64) (storageBase : Z) (total : nat)
      (storageBytes : list (bv 8)) (storageTail : spec),
    writeSuccessStorageKeysLoopSpec x19
      (writeSuccessAccessListsStorageFrame
        x19 P sp storageBase total storageBytes storageTail))%I.

Global Instance : LithiumUnfold
    (@writeSuccessAccessListsStorageAnyLoopSpec) := I.

Lemma write_success_byte_array_to_uninit `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) :
  base ↦ₘ∗ bytes -∗ base ↦ₘ? Z.of_nat (length bytes).
Proof.
  iIntros "Hbytes".
  iPoseProof (mem_mapsto_byte_array_to_mapsto base (DfracOwn 1) bytes
    with "Hbytes") as "Hword".
  iPoseProof (mem_mapsto_mapsto_to_uninit with "Hword") as "Huninit".
  have Hsize :
      Z.of_N ((Z.to_N (Z.of_nat (length bytes)) * 8) `div` 8) =
      Z.of_nat (length bytes).
  { rewrite N.div_mul; [rewrite Z2N.id; lia | lia]. }
  iEval (rewrite Hsize) in "Huninit".
  iExact "Huninit".
Qed.

Lemma write_success_access_lists_storage_exit
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma)
    (sp : bv 64) (storageBase : Z) (total : nat)
    (storageBytes : list (bv 8)) (tail : spec) :
  writeSuccessStorageKeysLoopExit x19 sp storageBase total storageBytes tail
    (writeSuccessAccessListsStorageFrame
      x19 P sp storageBase total storageBytes tail) -∗
  writeSuccessAccessListsTailSpec x19 P.
Proof.
  iIntros "Hexit".
  iDestruct "Hexit" as
    (pointer)
    "(Hsys & Hother & Hx19 & Hx2 & Hx22 & Hx27 & HstorageBytes & Hstorage &
      Hmmio & Htrace & Hframe & %Hpointer & _)".
  iDestruct "Hframe" as
    (accessBase entry entries processed remaining bytes prefix suffix
      x10 x11 savedX22 finalTail)
    "(Hprefix & Hsuffix & Hprocessed & Hremaining & Hsaved & Hbase &
      Htotal & Hindex & Hcopied & Houtput & %HentryValid & %HstorageBase &
      %HstorageCount & %HtotalNonzero & %HstorageBytesEq & %HstorageLow &
      %HstorageHigh & %Htail & HP & Hinv & HaccessExit & _)".
  iEval (rewrite HstorageBase HstorageBytesEq) in "HstorageBytes".
  iAssert (writeSuccessAccessEntryStorageOwn entry)%I
    with "[HstorageBytes]" as "HentryStorage".
  { destruct (writeSuccessAccessEntryStorageCount entry) as [|count] eqn:Hcount.
    - exfalso. apply HtotalNonzero. exact HstorageCount.
    - rewrite /writeSuccessAccessEntryStorageOwn Hcount.
      iFrame.
      iSplit; [iPureIntro; exact HstorageLow |].
      iSplit; [iPureIntro; exact HstorageHigh |].
      done. }
  iAssert (writeSuccessAccessEntryOwn entry)%I with "[HentryStorage]"
    as "HentryOwn".
  { rewrite /writeSuccessAccessEntryOwn. iFrame. done. }
  iAssert (writeSuccessAccessListsScratch sp accessBase (length entries)
      (Z_to_bv 64 (Z.of_nat (length processed))) savedX22)%I
    with "[Hsaved Hbase Htotal Hindex Hcopied Houtput Hstorage]" as
    "Hscratch".
  { iPoseProof (write_success_byte_array_to_uninit
      (bv_unsigned sp + 1744) (writeSuccessAccessEntryBytes entry)
      with "Hcopied") as "Hcopied".
    iEval (rewrite (proj1 HentryValid)) in "Hcopied".
    rewrite /writeSuccessAccessListsScratch. iFrame. }
  iEval (rewrite Htail) in "Htrace".
  iEval (rewrite /reg_col; cbn) in "Hother".
  iDestruct "Hother" as
    "(H1 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 &
      H13 & H14 & H15 & H16 & H17 & H18 & H20 & H21 & H23 & H24 &
      H25 & H26 & H28 & H29 & H30 & H31 & _)".
  iDestruct "H10" as (v10) "[%Hv10 Hx10]".
  iDestruct "H11" as (v11) "[%Hv11 Hx11]".
  destruct (valu_has_bits_shape v10 64 Hv10) as [b10 ->].
  destruct (valu_has_bits_shape v11 64 Hv11) as [b11 ->].
  iExists sp, accessBase, entry, entries, processed, remaining, bytes,
    prefix, suffix, savedX22, b10, b11, pointer, (BV 64 0), finalTail.
  rewrite /reg_col. cbn.
  iFrame "Hsys Hx2 Hprefix Hsuffix Hprocessed Hremaining Hscratch Hmmio
    HP Hinv HaccessExit HentryOwn Hx19".
  iFrame "H1 H3 H4 H5 H6 H7 H8 H9 H12 H13 H14 H15 H16 H17 H18 H20
    H21 H23 H24 H25 H26 H28 H29 H30 H31 Hx10 Hx11 Hx22 Hx27 Htrace".
Qed.
