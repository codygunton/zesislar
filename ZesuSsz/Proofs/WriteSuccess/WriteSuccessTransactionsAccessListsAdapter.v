Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary153c0.

Import ListNotations.

Lemma write_success_transactions_access_to_split `{!islaG Sigma}
    (sp : bv 64) (transaction : writeSuccessTransaction) :
  (match writeSuccessTransactionTo transaction with
   | Some _ =>
       (bv_unsigned sp + 1744) ↦ₘ writeSuccessTransactionWord transaction 265 ∗
       (bv_unsigned sp + 1752) ↦ₘ writeSuccessTransactionWord transaction 273 ∗
       (bv_unsigned sp + 1760) ↦ₘ
         bv_extract 0 32
           (bv_sign_extend 64
            (bv_extract 0 32
             (bv_or
             (bv_or
               (bv_zero_extend 64 (writeSuccessTransactionByte transaction 284) ≪ 24)
               (bv_zero_extend 64 (writeSuccessTransactionByte transaction 283) ≪ 16))
             (bv_or
               (bv_zero_extend 64 (writeSuccessTransactionByte transaction 282) ≪ 8)
               (bv_zero_extend 64 (writeSuccessTransactionByte transaction 281)))))) ∗
       (bv_unsigned sp + 1764) ↦ₘ? 132
   | None =>
       (bv_unsigned sp + 1744) ↦ₘ writeSuccessTransactionByte transaction 264 ∗
       (bv_unsigned sp + 1745) ↦ₘ? 151
   end) -∗
  (bv_unsigned sp + 1744) ↦ₘ? 40 ∗
  ((bv_unsigned sp + 1744) ↦ₘ? 40 -∗
   (bv_unsigned sp + 1744) ↦ₘ? 152).
Proof.
  iIntros "Hto".
  destruct (writeSuccessTransactionTo transaction) as [address|] eqn:Hcase.
  - iDestruct "Hto" as "(H0 & H8 & H16 & H20)".
    iAssert ((bv_unsigned sp + 1744) ↦ₘ? 8)%I with "[H0]" as "H0".
    { iApply (mem_mapsto_mapsto_to_uninit with "H0"). }
    iAssert ((bv_unsigned sp + 1752) ↦ₘ? 8)%I with "[H8]" as "H8".
    { iApply (mem_mapsto_mapsto_to_uninit with "H8"). }
    iAssert ((bv_unsigned sp + 1760) ↦ₘ? 4)%I with "[H16]" as "H16".
    { iApply (mem_mapsto_mapsto_to_uninit with "H16"). }
    iDestruct (mem_mapsto_uninit_split 20 with "H20") as "[H20 H40]";
      first lia.
    have A8 : bv_unsigned sp + 1744 + 8 = bv_unsigned sp + 1752 by lia.
    have A16 : bv_unsigned sp + 1744 + 16 = bv_unsigned sp + 1760 by lia.
    have A20 : bv_unsigned sp + 1760 + 4 = bv_unsigned sp + 1764 by lia.
    have A40 : bv_unsigned sp + 1764 + 20 = bv_unsigned sp + 1784 by lia.
    iEval (rewrite <- A8) in "H8". iEval (rewrite <- A20) in "H20".
    iEval (rewrite A40) in "H40".
    iEval (replace (132 - 20)%Z with 112%Z by lia) in "H40".
    have Aend : bv_unsigned sp + 1744 + 40 = bv_unsigned sp + 1784 by lia.
    iEval (rewrite <- Aend) in "H40".
    iAssert ((bv_unsigned sp + 1744) ↦ₘ? 16)%I with "[H0 H8]" as "H0".
    { iApply (mem_mapsto_uninit_combine 8 with "[H0] [H8]");
      [lia | iExact "H0" | iExact "H8"]. }
    iAssert ((bv_unsigned sp + 1760) ↦ₘ? 24)%I with "[H16 H20]" as "H16".
    { iApply (mem_mapsto_uninit_combine 4 with "[H16] [H20]");
      [lia | iExact "H16" | iExact "H20"]. }
    iEval (rewrite <- A16) in "H16".
    iAssert ((bv_unsigned sp + 1744) ↦ₘ? 40)%I with "[H0 H16]" as "H0".
    { iApply (mem_mapsto_uninit_combine 16 with "[H0] [H16]");
      [lia | iExact "H0" | iExact "H16"]. }
    iFrame "H0". iIntros "H0".
    iApply (mem_mapsto_uninit_combine 40 with "[H0] [H40]");
      [lia | iExact "H0" | iExact "H40"].
  - iDestruct "Hto" as "(H0 & H1)".
    iAssert ((bv_unsigned sp + 1744) ↦ₘ? 1)%I with "[H0]" as "H0".
    { iApply (mem_mapsto_mapsto_to_uninit with "H0"). }
    iDestruct (mem_mapsto_uninit_split 39 with "H1") as "[H1 H40]";
      first lia.
    have A1 : bv_unsigned sp + 1744 + 1 = bv_unsigned sp + 1745 by lia.
    have A40 : bv_unsigned sp + 1745 + 39 = bv_unsigned sp + 1784 by lia.
    iEval (rewrite <- A1) in "H1". iEval (rewrite A40) in "H40".
    iEval (replace (151 - 39)%Z with 112%Z by lia) in "H40".
    have Aend : bv_unsigned sp + 1744 + 40 = bv_unsigned sp + 1784 by lia.
    iEval (rewrite <- Aend) in "H40".
    iAssert ((bv_unsigned sp + 1744) ↦ₘ? 40)%I with "[H0 H1]" as "H0".
    { iApply (mem_mapsto_uninit_combine 1 with "[H0] [H1]");
      [lia | iExact "H0" | iExact "H1"]. }
    iFrame "H0". iIntros "H0".
    iApply (mem_mapsto_uninit_combine 40 with "[H0] [H40]");
      [lia | iExact "H0" | iExact "H40"].
Qed.

Lemma write_success_transactions_access_storage_split_core `{!islaG Sigma}
    (sp : bv 64) :
  (bv_unsigned sp + 1680) ↦ₘ? 64 -∗
  writeSuccessStorageKeysScratch sp ∗
  (writeSuccessStorageKeysScratch sp -∗ (bv_unsigned sp + 1680) ↦ₘ? 64).
Proof.
  iIntros "H".
  iDestruct (mem_mapsto_uninit_split 32 with "H") as "[Hprefix H]"; first lia.
  have A : bv_unsigned sp + 1680 + 32 = bv_unsigned sp + 1712 by lia.
  iEval (rewrite A) in "H".
  iDestruct (mem_mapsto_uninit_split 8 with "H") as "[H0 H]"; first lia.
  iDestruct (mem_mapsto_uninit_split 8 with "H") as "[H1 H]"; first lia.
  iDestruct (mem_mapsto_uninit_split 8 with "H") as "[H2 H3]"; first lia.
  iEval (replace (bv_unsigned sp + 1712 + 8)%Z with
    (bv_unsigned sp + 1720)%Z by lia) in "H1".
  iEval (replace (bv_unsigned sp + 1712 + 8 + 8)%Z with
    (bv_unsigned sp + 1728)%Z by lia) in "H2".
  iEval (replace (bv_unsigned sp + 1712 + 8 + 8 + 8)%Z with
    (bv_unsigned sp + 1736)%Z by lia) in "H3".
  iDestruct (mem_mapsto_uninit_to_mapsto with "H0") as (n0 w0 Hn0) "H0".
  iDestruct (mem_mapsto_uninit_to_mapsto with "H1") as (n1 w1 Hn1) "H1".
  iDestruct (mem_mapsto_uninit_to_mapsto with "H2") as (n2 w2 Hn2) "H2".
  iDestruct (mem_mapsto_uninit_to_mapsto with "H3") as (n3 w3 Hn3) "H3".
  cbn in Hn0, Hn1, Hn2, Hn3. subst n0 n1 n2 n3.
  iSplitL "H0 H1 H2 H3".
  { rewrite /writeSuccessStorageKeysScratch. iExists w0, w1, w2, w3. iFrame. }
  iIntros "(%v0 & %v1 & %v2 & %v3 & H0 & H1 & H2 & H3 & _)".
  iAssert ((bv_unsigned sp + 1712) ↦ₘ? 8)%I with "[H0]" as "H0".
  { iApply (mem_mapsto_mapsto_to_uninit with "H0"). }
  iAssert ((bv_unsigned sp + 1720) ↦ₘ? 8)%I with "[H1]" as "H1".
  { iApply (mem_mapsto_mapsto_to_uninit with "H1"). }
  iAssert ((bv_unsigned sp + 1728) ↦ₘ? 8)%I with "[H2]" as "H2".
  { iApply (mem_mapsto_mapsto_to_uninit with "H2"). }
  iAssert ((bv_unsigned sp + 1736) ↦ₘ? 8)%I with "[H3]" as "H3".
  { iApply (mem_mapsto_mapsto_to_uninit with "H3"). }
  have A1 : bv_unsigned sp + 1712 + 8 = bv_unsigned sp + 1720 by lia.
  have A2 : bv_unsigned sp + 1712 + 16 = bv_unsigned sp + 1728 by lia.
  have A3 : bv_unsigned sp + 1728 + 8 = bv_unsigned sp + 1736 by lia.
  iEval (rewrite <- A1) in "H1". iEval (rewrite <- A3) in "H3".
  iAssert ((bv_unsigned sp + 1712) ↦ₘ? 16)%I with "[H0 H1]" as "H01".
  { iApply (mem_mapsto_uninit_combine 8 with "[H0] [H1]");
    [lia | iExact "H0" | iExact "H1"]. }
  iAssert ((bv_unsigned sp + 1728) ↦ₘ? 16)%I with "[H2 H3]" as "H23".
  { iApply (mem_mapsto_uninit_combine 8 with "[H2] [H3]");
    [lia | iExact "H2" | iExact "H3"]. }
  iEval (rewrite <- A2) in "H23".
  iAssert ((bv_unsigned sp + 1712) ↦ₘ? 32)%I with "[H01 H23]" as "Htail".
  { iApply (mem_mapsto_uninit_combine 16 with "[H01] [H23]");
    [lia | iExact "H01" | iExact "H23"]. }
  iEval (rewrite <- A) in "Htail".
  iApply (mem_mapsto_uninit_combine 32 with "[Hprefix] [Htail]");
    [lia | iExact "Hprefix" | iExact "Htail"].
Qed.

Lemma write_success_transactions_access_scratch_split
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction)
    (accessBase : Z) (accessTotal : nat)
    (Hbase : writeSuccessTransactionWord transaction 208 = Z_to_bv 64 accessBase)
    (Htotal : writeSuccessTransactionWord transaction 216 =
      Z_to_bv 64 (Z.of_nat accessTotal)) :
  writeSuccessTransactionsScratch1519c sp base transactions processed transaction -∗
  writeSuccessAccessListsScratch sp accessBase accessTotal
    (writeSuccessTransactionWord transaction 176)
    (writeSuccessTransactionWord transaction 232) ∗
  (∀ storedIndex : bv 64,
   writeSuccessAccessListsScratch sp accessBase accessTotal
     storedIndex (writeSuccessTransactionWord transaction 232) -∗
   writeSuccessTransactionsScratch153c0 sp base transactions processed transaction).
Proof.
  iIntros "(Hlower & H104 & H112 & H120 & H128 & H136 & H144 & H152 &
    H160 & H168 & H176 & H184 & H192 & H200 & H208 & H216 & H224 & H232 &
    H240 & H248 & H256 & H264 & H272 & H280 & H1640 & H1648 & H1656 &
    H1660 & H1664 & H1672 & H1680 & Hto & _)".
  iDestruct (mem_mapsto_uninit_split 32 with "Hlower") as "[Hlower32 Hlower]";
    first lia.
  have Aminus16 : bv_unsigned sp - 48 + 32 = bv_unsigned sp - 16 by lia.
  iEval (rewrite Aminus16) in "Hlower".
  iDestruct (mem_mapsto_uninit_split 16 with "Hlower") as "[Hstack16 Hlower104]";
    first lia.
  have Azero : bv_unsigned sp - 16 + 16 = bv_unsigned sp by lia.
  iEval (rewrite Azero) in "Hlower104".
  iPoseProof (write_success_transactions_access_storage_split_core sp with "H1680")
    as "(Hstorage & HstorageRestore)".
  iPoseProof (write_success_transactions_access_to_split sp transaction with "Hto")
    as "(Hto40 & HtoRestore)".
  iSplitL "H136 H256 H264 H272 Hto40 Hstack16 Hstorage".
  { rewrite /writeSuccessAccessListsScratch Hbase Htotal. iFrame. }
  iIntros (restoredIndex)
    "(H136 & H256 & H264 & H272 & Hto40 & Hstack16 & Hstorage & _)".
  iDestruct ("HstorageRestore" with "Hstorage") as "H1680".
  iDestruct ("HtoRestore" with "Hto40") as "H1744".
  iAssert ((bv_unsigned sp - 48) ↦ₘ? 152)%I
    with "[Hlower32 Hstack16 Hlower104]" as "Hlower".
  { iAssert ((bv_unsigned sp - 16) ↦ₘ? 120)%I
      with "[Hstack16 Hlower104]" as "Htail".
    { iEval (rewrite <- Azero) in "Hlower104".
      iApply (mem_mapsto_uninit_combine 16 with "[Hstack16] [Hlower104]");
        [lia | iExact "Hstack16" | iExact "Hlower104"]. }
    iEval (rewrite <- Aminus16) in "Htail".
    iApply (mem_mapsto_uninit_combine 32 with "[Hlower32] [Htail]");
      [lia | iExact "Hlower32" | iExact "Htail"]. }
  iAssert ((bv_unsigned sp + 272) ↦ₘ? 8)%I with "[H272]" as "H272".
  { iApply (mem_mapsto_mapsto_to_uninit with "H272"). }
  iAssert ((bv_unsigned sp + 1640) ↦ₘ? 8)%I with "[H1640]" as "H1640".
  { iApply (mem_mapsto_mapsto_to_uninit with "H1640"). }
  iAssert ((bv_unsigned sp + 1648) ↦ₘ? 8)%I with "[H1648]" as "H1648".
  { iApply (mem_mapsto_mapsto_to_uninit with "H1648"). }
  iAssert ((bv_unsigned sp + 1656) ↦ₘ? 4)%I with "[H1656]" as "H1656".
  { iApply (mem_mapsto_mapsto_to_uninit with "H1656"). }
  iAssert ((bv_unsigned sp + 1664) ↦ₘ? 8)%I with "[H1664]" as "H1664".
  { iApply (mem_mapsto_mapsto_to_uninit with "H1664"). }
  iAssert ((bv_unsigned sp + 1672) ↦ₘ? 8)%I with "[H1672]" as "H1672".
  { iApply (mem_mapsto_mapsto_to_uninit with "H1672"). }
  have A1648 : bv_unsigned sp + 1640 + 8 = bv_unsigned sp + 1648 by lia.
  have A1656 : bv_unsigned sp + 1640 + 16 = bv_unsigned sp + 1656 by lia.
  have A1664 : bv_unsigned sp + 1640 + 24 = bv_unsigned sp + 1664 by lia.
  have A1672 : bv_unsigned sp + 1640 + 32 = bv_unsigned sp + 1672 by lia.
  iEval (rewrite <- A1648) in "H1648".
  iAssert ((bv_unsigned sp + 1640) ↦ₘ? 16)%I with "[H1640 H1648]" as "H1640".
  { iApply (mem_mapsto_uninit_combine 8 with "[H1640] [H1648]");
      [lia | iExact "H1640" | iExact "H1648"]. }
  iAssert ((bv_unsigned sp + 1656) ↦ₘ? 8)%I with "[H1656 H1660]" as "H1656".
  { have A1660 : bv_unsigned sp + 1656 + 4 = bv_unsigned sp + 1660 by lia.
    iEval (rewrite <- A1660) in "H1660".
    iApply (mem_mapsto_uninit_combine 4 with "[H1656] [H1660]");
      [lia | iExact "H1656" | iExact "H1660"]. }
  iEval (rewrite <- A1656) in "H1656".
  iAssert ((bv_unsigned sp + 1640) ↦ₘ? 24)%I with "[H1640 H1656]" as "H1640".
  { iApply (mem_mapsto_uninit_combine 16 with "[H1640] [H1656]");
      [lia | iExact "H1640" | iExact "H1656"]. }
  iAssert ((bv_unsigned sp + 1664) ↦ₘ? 16)%I with "[H1664 H1672]" as "H1664".
  { have A1672b : bv_unsigned sp + 1664 + 8 = bv_unsigned sp + 1672 by lia.
    iEval (rewrite <- A1672b) in "H1672".
    iApply (mem_mapsto_uninit_combine 8 with "[H1664] [H1672]");
      [lia | iExact "H1664" | iExact "H1672"]. }
  iEval (rewrite <- A1664) in "H1664".
  iAssert ((bv_unsigned sp + 1640) ↦ₘ? 40)%I with "[H1640 H1664]" as "H1640".
  { iApply (mem_mapsto_uninit_combine 24 with "[H1640] [H1664]");
      [lia | iExact "H1640" | iExact "H1664"]. }
  have A1640 : bv_unsigned sp + 280 + 1360 = bv_unsigned sp + 1640 by lia.
  iEval (rewrite <- A1640) in "H1640".
  iAssert ((bv_unsigned sp + 280) ↦ₘ? 1400)%I with "[H280 H1640]" as "Hupper".
  { iApply (mem_mapsto_uninit_combine 1360 with "[H280] [H1640]");
      [lia | iExact "H280" | iExact "H1640"]. }
  have A1680 : bv_unsigned sp + 280 + 1400 = bv_unsigned sp + 1680 by lia.
  iEval (rewrite <- A1680) in "H1680".
  iAssert ((bv_unsigned sp + 280) ↦ₘ? 1464)%I with "[Hupper H1680]" as "Hupper".
  { iApply (mem_mapsto_uninit_combine 1400 with "[Hupper] [H1680]");
      [lia | iExact "Hupper" | iExact "H1680"]. }
  have A1744 : bv_unsigned sp + 280 + 1464 = bv_unsigned sp + 1744 by lia.
  iEval (rewrite <- A1744) in "H1744".
  iAssert ((bv_unsigned sp + 280) ↦ₘ? 1616)%I with "[Hupper H1744]" as "Hupper".
  { iApply (mem_mapsto_uninit_combine 1464 with "[Hupper] [H1744]");
      [lia | iExact "Hupper" | iExact "H1744"]. }
  rewrite /writeSuccessTransactionsScratch153c0.
  rewrite Hbase Htotal.
  iFrame.
Qed.

Lemma write_success_transactions_access_entries_length `{!islaG Sigma}
    (entries : list writeSuccessAccessEntry) :
  writeSuccessAccessEntriesOwn entries -∗
  ⌜length (writeSuccessAccessEntriesBytes entries) =
    (40 * length entries)%nat⌝ ∗
  writeSuccessAccessEntriesOwn entries.
Proof.
  induction entries as [|entry entries IH].
  - iIntros "_". iSplit; [done | done].
  - iIntros "(Hentry & Hentries & _)".
    iDestruct "Hentry" as "(Hstorage & %Hvalid & _)".
    iPoseProof (IH with "Hentries") as "(%Hlength & Hentries)".
    iSplit.
    + iPureIntro. cbn. rewrite app_length.
      unfold writeSuccessAccessEntryValid in Hvalid. lia.
    + cbn. iFrame. done.
Qed.

Lemma write_success_transactions_access_empty_array `{!islaG Sigma} (base : Z) :
  ⌜0 <= base <= 2 ^ 64⌝ -∗ base ↦ₘ∗ ([] : list (bv 8)).
Proof.
  iIntros "%Hbase".
  rewrite mem_mapsto_array_eq /mem_mapsto_array_def.
  iExists 1%N. repeat iSplit; try done; iPureIntro; cbn; lia.
Qed.

Definition writeSuccessTransactionsAccessEntryResources
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) : iProp Sigma :=
  (bv_unsigned (writeSuccessTransactionWord transaction 208) ↦ₘ∗
      ([] : list (bv 8)) ∗
   bv_unsigned (writeSuccessTransactionWord transaction 208) ↦ₘ∗
      writeSuccessAccessEntriesBytes
        (writeSuccessTransactionAccessEntries transaction) ∗
   writeSuccessAccessEntriesOwn
      (writeSuccessTransactionAccessEntries transaction) ∗
   (bv_unsigned (writeSuccessTransactionWord transaction 208) ↦ₘ∗
        writeSuccessAccessEntriesBytes
          (writeSuccessTransactionAccessEntries transaction) -∗
    writeSuccessAccessEntriesOwn
        (writeSuccessTransactionAccessEntries transaction) -∗
    writeSuccessTransactionOwn transaction) ∗
   writeSuccessAccessListsInvariant sp
      (bv_unsigned (writeSuccessTransactionWord transaction 208))
      (writeSuccessTransactionAccessEntries transaction) []
      (writeSuccessTransactionAccessEntries transaction)
      (writeSuccessAccessEntriesBytes
        (writeSuccessTransactionAccessEntries transaction)) []
      (writeSuccessAccessEntriesBytes
        (writeSuccessTransactionAccessEntries transaction)) ∗
   writeSuccessTransactionsInvariant sp base transactions processed
      (transaction :: remaining) bytes prefix suffix ∗
   ⌜writeSuccessTransactionWord transaction 208 =
      Z_to_bv 64
        (bv_unsigned (writeSuccessTransactionWord transaction 208))⌝ ∗
   ⌜writeSuccessTransactionWord transaction 216 =
      Z_to_bv 64
        (Z.of_nat
          (length (writeSuccessTransactionAccessEntries transaction)))⌝ ∗
   ⌜writeSuccessTransactionAccessBytes transaction =
      writeSuccessAccessEntriesBytes
        (writeSuccessTransactionAccessEntries transaction)⌝)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAccessEntryResources) := I.

Definition writeSuccessTransactionsAccessFrame
    `{!islaG Sigma} `{!threadG}
    (accessSp : bv 64) (accessBase : Z)
    (accessEntries : list writeSuccessAccessEntry)
    (accessBytes : list (bv 8)) (accessTail : spec)
    (accessX19 savedX22 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    (∀ storedIndex : bv 64,
     writeSuccessAccessListsScratch sp accessBase (length accessEntries)
       storedIndex savedX22 -∗
     writeSuccessTransactionsScratch153c0
       sp base transactions processed transaction) ∗
    (accessBase ↦ₘ∗ accessBytes -∗
     writeSuccessAccessEntriesOwn accessEntries -∗
     writeSuccessTransactionOwn transaction) ∗
    base ↦ₘ∗ prefix ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
    writeSuccessTransactionsProcessedOwn processed ∗
    writeSuccessTransactionsOwn remaining ∗ P ∗
    writeSuccessTransactionsInvariant sp base transactions processed
      (transaction :: remaining) bytes prefix suffix ∗
    instr_pre writeSuccessTransactionsLoopExitAddress
      (writeSuccessTransactionsLoopExit sp base transactions bytes tail P) ∗
    ⌜accessSp = sp⌝ ∗
    ⌜accessEntries = writeSuccessTransactionAccessEntries transaction⌝ ∗
    ⌜accessBytes = writeSuccessTransactionAccessBytes transaction⌝ ∗
    ⌜accessTail =
      writeSuccessTransactionPhaseEvents TransactionBlobCount sp transaction
        (writeSuccessTransactionsEvents sp remaining tail)⌝ ∗
    ⌜accessX19 = writeSuccessTransactionWord transaction 224⌝ ∗
    ⌜savedX22 = writeSuccessTransactionWord transaction 232⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAccessFrame) := I.

Lemma write_success_transactions_access_exit
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (accessBase : Z)
    (entries : list writeSuccessAccessEntry) (accessBytes : list (bv 8))
    (accessTail : spec) (x19 savedX22 : bv 64) (P : iProp Sigma) :
  instr_body 0x153c0 (writeSuccessTransactionsAt153c0Spec P) -∗
  instr_pre 0x153c0
    (writeSuccessAccessListsLoopExit sp accessBase entries accessBytes
      accessTail x19 savedX22
      (writeSuccessTransactionsAccessFrame sp accessBase entries accessBytes
        accessTail x19 savedX22 P)).
Proof.
  iIntros "Hnext".
  iApply (instr_pre_wand 0x153c0 0x153c0 false true with "Hnext");
    [done | done |].
  iIntros "(%storedIndex & %x22 & %x27 & Hsys & Hregs & H2 & H19 & H10 &
    H11 & H22 & H27 & HaccessBytes & Hentries & Hscratch & Hmmio & Htrace &
    Hframe & _)".
  iDestruct "Hframe" as
    "(%txSp & %base & %transaction & %transactions & %processed & %remaining &
      %bytes & %prefix & %suffix & %tail & HscratchRestore &
      HtransactionRestore & Hprefix & Hsuffix & Hprocessed & Hremaining & HP &
      Hinvariant & Hexit & %Hsp & %Hentries & %Hbytes & %Htail & %Hx19 &
      %Hsaved & _)".
  subst sp entries accessBytes accessTail x19 savedX22.
  iDestruct ("HscratchRestore" $! storedIndex with "Hscratch") as "Hscratch".
  iDestruct ("HtransactionRestore" with "HaccessBytes Hentries") as
    "Htransaction".
  iEval (rewrite /writeSuccessTransactionsInvariant) in "Hinvariant".
  iDestruct "Hinvariant" as
    "(HtransactionsEq & HbytesEq & HprefixEq & HsuffixEq & HbytesAppend &
      HbytesLength & HprefixLength & HsuffixLength & HtransactionsBound &
      %Halign16 & %HspLow & %HspHigh & HbaseAlign & HbaseLow & HbaseHigh & _)".
  have Halign8 : bv_unsigned txSp `mod` 8 = 0 by lia.
  iAssert (reg_col writeSuccessTransactions153c0OtherRegShapes)%I
    with "[Hregs H22 H27]" as "HtargetRegs".
  { iEval (rewrite /writeSuccessAccessListsOtherRegShapes /reg_col; cbn)
      in "Hregs".
    iDestruct "Hregs" as
      "(H1 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H12 & H13 & H14 & H15 &
        H16 & H17 & H18 & H20 & H21 & H23 & H24 & H25 & H26 & H28 & H29 &
        H30 & H31 & _)".
    rewrite /writeSuccessTransactions153c0OtherRegShapes /reg_col /=.
    iFrame.
    repeat iSplit; try iPureIntro; done. }
  iExists txSp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iAssert (writeSuccessTransactionsInvariant txSp base transactions processed
      (transaction :: remaining) bytes prefix suffix)%I
    with "[HtransactionsEq HbytesEq HprefixEq HsuffixEq HbytesAppend
      HbytesLength HprefixLength HsuffixLength HtransactionsBound HbaseAlign
      HbaseLow HbaseHigh]" as "Hinvariant".
  { rewrite /writeSuccessTransactionsInvariant.
    iFrame "HtransactionsEq HbytesEq HprefixEq HsuffixEq HbytesAppend
      HbytesLength HprefixLength HsuffixLength HtransactionsBound HbaseAlign
      HbaseLow HbaseHigh".
    repeat iSplit; try iPureIntro; try assumption; done. }
  rewrite /writeSuccessTransactionPhaseHandoff
    /writeSuccessTransactionsMachine153c0.
  iFrame "Hsys HtargetRegs H2 H10 H11 H19 Hscratch Hprefix Hsuffix Hprocessed
    Htransaction Hremaining Hmmio Htrace HP Hinvariant Hexit".
  repeat iSplit; try done.
  all: iPureIntro; lia.
Qed.
