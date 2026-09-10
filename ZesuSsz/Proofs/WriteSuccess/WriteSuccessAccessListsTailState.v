From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsTailBoundaries.

Import ListNotations.

Lemma write_success_access_entries_own_snoc
    `{!islaG Sigma} (processed : list writeSuccessAccessEntry)
    (entry : writeSuccessAccessEntry) :
  writeSuccessAccessEntriesOwn processed -∗
  writeSuccessAccessEntryOwn entry -∗
  writeSuccessAccessEntriesOwn (processed ++ [entry]).
Proof.
  induction processed as [|current processed IH]; simpl.
  - iIntros "_ Hentry". iFrame. done.
  - iIntros "Hprocessed Hentry".
    iDestruct "Hprocessed" as "(Hcurrent & Hprocessed & _)".
    iFrame "Hcurrent".
    iPoseProof (IH with "Hprocessed Hentry") as "Hsnoc".
    iFrame "Hsnoc".
Qed.

Lemma write_success_access_entries_bytes_app
    (left right : list writeSuccessAccessEntry) :
  writeSuccessAccessEntriesBytes (left ++ right) =
  writeSuccessAccessEntriesBytes left ++ writeSuccessAccessEntriesBytes right.
Proof.
  induction left as [|entry left IH]; simpl; [reflexivity|].
  rewrite IH app_assoc. reflexivity.
Qed.

Lemma write_success_access_entries_bytes_snoc
    (processed : list writeSuccessAccessEntry) (entry : writeSuccessAccessEntry) :
  writeSuccessAccessEntriesBytes (processed ++ [entry]) =
    writeSuccessAccessEntriesBytes processed ++ writeSuccessAccessEntryBytes entry.
Proof.
  rewrite write_success_access_entries_bytes_app. cbn.
  now rewrite app_nil_r.
Qed.

Lemma write_success_access_entries_bytes_length_snoc
    (processed : list writeSuccessAccessEntry) (entry : writeSuccessAccessEntry) :
  length (writeSuccessAccessEntriesBytes processed) =
      (40 * length processed)%nat ->
  length (writeSuccessAccessEntryBytes entry) = 40%nat ->
  length (writeSuccessAccessEntriesBytes (processed ++ [entry])) =
      (40 * length (processed ++ [entry]))%nat.
Proof.
  intros Hprocessed Hentry.
  rewrite write_success_access_entries_bytes_snoc length_app Hprocessed Hentry.
  rewrite app_length. cbn. lia.
Qed.

Lemma write_success_access_entries_bytes_length_tail
    (entry : writeSuccessAccessEntry) (remaining : list writeSuccessAccessEntry) :
  length (writeSuccessAccessEntryBytes entry) = 40%nat ->
  length (writeSuccessAccessEntriesBytes (entry :: remaining)) =
      (40 * length (entry :: remaining))%nat ->
  length (writeSuccessAccessEntriesBytes remaining) =
      (40 * length remaining)%nat.
Proof.
  intros Hentry Htail.
  cbn [writeSuccessAccessEntriesBytes] in Htail.
  rewrite length_app Hentry in Htail. cbn in Htail. lia.
Qed.

Lemma write_success_access_lists_x11_snoc
    (processed : list writeSuccessAccessEntry) (entry : writeSuccessAccessEntry) :
  (Z_to_bv 64 (Z.of_nat (length processed)) + 1)%bv =
  Z_to_bv 64 (Z.of_nat (length (processed ++ [entry]))).
Proof. rewrite app_length. cbn. bv_solve. Qed.

Lemma write_success_split_access_memory_entry `{!islaG Sigma}
    (base : Z) (processed : list writeSuccessAccessEntry)
    (entry : writeSuccessAccessEntry) (remainingBytes : list (bv 8))
    (HentryLength : length (writeSuccessAccessEntryBytes entry) = 40%nat) :
  (base + 40 * Z.of_nat (length processed)) ↦ₘ∗
      (writeSuccessAccessEntryBytes entry ++ remainingBytes) -∗
  (base + 40 * Z.of_nat (length processed)) ↦ₘ∗
      writeSuccessAccessEntryBytes entry ∗
  (base + 40 * Z.of_nat (length (processed ++ [entry]))) ↦ₘ∗ remainingBytes.
Proof.
  iIntros "Hmemory".
  iDestruct (mem_mapsto_array_app 8%N
    (base + 40 * Z.of_nat (length processed)) (DfracOwn 1)
    (writeSuccessAccessEntryBytes entry) remainingBytes with "Hmemory")
    as "[Hentry Hremaining]".
  iFrame "Hentry".
  have Haddress :
      (base + 40 * Z.of_nat (length processed) +
        Z.of_N (8 `div` 8) * length (writeSuccessAccessEntryBytes entry))%Z =
      (base + 40 * Z.of_nat (length (processed ++ [entry])))%Z.
  { rewrite HentryLength app_length. cbn.
    replace (Z.of_N (8 `div` 8)) with 1%Z by reflexivity.
    rewrite Nat2Z.inj_add. lia. }
  iEval (rewrite Haddress) in "Hremaining".
  iExact "Hremaining".
Qed.

Lemma write_success_combine_access_memory_processed `{!islaG Sigma}
    (base : Z) (processed : list writeSuccessAccessEntry)
    (leftBytes rightBytes : list (bv 8))
    (Hlength : length leftBytes = (40 * length processed)%nat) :
  base ↦ₘ∗ leftBytes -∗
  (base + 40 * Z.of_nat (length processed)) ↦ₘ∗ rightBytes -∗
  base ↦ₘ∗ (leftBytes ++ rightBytes).
Proof.
  iIntros "Hleft Hright".
  iApply (mem_mapsto_array_app_combine_at 8%N base (DfracOwn 1)
    leftBytes rightBytes (40 * length processed)%nat Hlength with "Hleft").
  replace (base + Z.of_N (8 `div` 8) * (40 * length processed)%nat)%Z
    with (base + 40 * Z.of_nat (length processed))%Z.
  - iExact "Hright".
  - replace (Z.of_N (8 `div` 8)) with 1%Z by reflexivity.
    rewrite Nat2Z.inj_mul. ring.
Qed.

Lemma write_success_access_lists_153bc_to_loop
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
  writeSuccessAccessListsAt153bcSpec x19 P -∗
  writeSuccessAccessListsLoopSpec x19 P.
Proof.
  iIntros "Hentry".
  iDestruct "Hentry" as
    (sp base entry entries processed remaining bytes prefix suffix
      savedX22 x10 x22 x27 tail)
    "(Hsys & Hx2 & Hx11 & Hindex & %HspAlign & %HspLow & %HspHigh &
      Hframe & _)".
  iDestruct "Hframe" as
    "(Hother & Hx10 & Hx19 & Hx22 & Hx27 & HbasePrefix & HbaseSuffix &
      Hprocessed & HentryOwn & Hremaining & Hscratch & Hmmio & Htrace &
      HP & Hinv & Hexit & _)".
  iDestruct "HentryOwn" as "(HstorageOwn & %HentryValid & _)".
  iDestruct "Hscratch" as
    "(Hsaved & Hbase & Htotal & Hcopied & Houtput & Hstorage & _)".
  iDestruct "Hinv" as
    "(%HentriesEq & %HbytesEq & %HprefixEq & %HsuffixEq & %HbytesSplit &
      %HbytesLength & %HprefixLength & %HsuffixLength & %HentriesBound &
      _ & _ & _ & %HbaseLow & %HbaseHigh & _)".
  have HentryLength : length (writeSuccessAccessEntryBytes entry) = 40%nat :=
    proj1 HentryValid.
  iEval (rewrite HsuffixEq; cbn [writeSuccessAccessEntriesBytes])
    in "HbaseSuffix".
  iDestruct (write_success_split_access_memory_entry base processed entry
    (writeSuccessAccessEntriesBytes remaining) HentryLength with
    "HbaseSuffix") as "[HentryBytes HremainingBytes]".
  have HprocessedBytesLength :
      length (writeSuccessAccessEntriesBytes processed) =
        (40 * length processed)%nat.
  { rewrite <- HprefixEq. exact HprefixLength. }
  iEval (rewrite HprefixEq) in "HbasePrefix".
  iPoseProof (write_success_combine_access_memory_processed base processed
    (writeSuccessAccessEntriesBytes processed)
    (writeSuccessAccessEntryBytes entry) HprocessedBytesLength with
    "HbasePrefix HentryBytes") as "HbasePrefixNew".
  iEval (rewrite <- (write_success_access_entries_bytes_snoc processed entry))
    in "HbasePrefixNew".
  iAssert (writeSuccessAccessEntryOwn entry)%I with "[HstorageOwn]"
    as "HentryOwn".
  { rewrite /writeSuccessAccessEntryOwn. iFrame. done. }
  iPoseProof (write_success_access_entries_own_snoc processed entry with
    "Hprocessed HentryOwn") as "HprocessedNew".
  have HentriesNew :
      entries = (processed ++ [entry]) ++ remaining.
  { rewrite HentriesEq -app_assoc. reflexivity. }
  have HbytesSplitNew :
      bytes = writeSuccessAccessEntriesBytes (processed ++ [entry]) ++
        writeSuccessAccessEntriesBytes remaining.
  { rewrite HbytesEq HentriesNew write_success_access_entries_bytes_app.
    reflexivity. }
  have HprefixLengthNew :
      length (writeSuccessAccessEntriesBytes (processed ++ [entry])) =
        (40 * length (processed ++ [entry]))%nat.
  { apply write_success_access_entries_bytes_length_snoc; assumption. }
  have HtailBytesLength :
      length (writeSuccessAccessEntriesBytes (entry :: remaining)) =
        (40 * length (entry :: remaining))%nat.
  { rewrite <- HsuffixEq. exact HsuffixLength. }
  have HsuffixLengthNew :
      length (writeSuccessAccessEntriesBytes remaining) =
        (40 * length remaining)%nat.
  { apply (write_success_access_entries_bytes_length_tail entry remaining);
      assumption. }
  iAssert (writeSuccessAccessListsScratch sp base (length entries)
      (Z_to_bv 64 (Z.of_nat (length processed))) savedX22)%I
    with "[Hsaved Hbase Htotal Hindex Hcopied Houtput Hstorage]" as
    "HscratchNew".
  { rewrite /writeSuccessAccessListsScratch. iFrame. }
  iAssert (writeSuccessAccessListsInvariant sp base entries
      (processed ++ [entry]) remaining bytes
      (writeSuccessAccessEntriesBytes (processed ++ [entry]))
      (writeSuccessAccessEntriesBytes remaining))%I with "[]" as "HinvNew".
  { rewrite /writeSuccessAccessListsInvariant.
    repeat iSplit; try iPureIntro; try reflexivity; try assumption; done. }
  iEval (rewrite (write_success_access_lists_x11_snoc processed entry))
    in "Hx11".
  iExists sp, base, entries, (processed ++ [entry]), remaining, bytes,
    (writeSuccessAccessEntriesBytes (processed ++ [entry])),
    (writeSuccessAccessEntriesBytes remaining),
    (Z_to_bv 64 (Z.of_nat (length processed))), savedX22,
    x10, x22, x27, tail.
  iFrame "Hsys Hother Hx2 Hx10 Hx19 Hx11 Hx22 Hx27 HbasePrefixNew
    HremainingBytes HprocessedNew Hremaining HscratchNew Hmmio Htrace HP
    HinvNew Hexit".
Qed.
