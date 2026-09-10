From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary151d0.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151d0Defs.

Lemma write_success_access_entries_own_length
    `{!islaG Sigma} (entries : list writeSuccessAccessEntry) :
  writeSuccessAccessEntriesOwn entries -∗
  ⌜length (writeSuccessAccessEntriesBytes entries) =
      (40 * length entries)%nat⌝ ∗
  writeSuccessAccessEntriesOwn entries.
Proof.
  induction entries as [|entry entries IH].
  - iIntros "_".
    iSplit; [iPureIntro; cbn; reflexivity|done].
  - iIntros "Hown".
    iDestruct "Hown" as "(Hentry & Hrest & _)".
    iDestruct "Hentry" as "(Hstorage & %Hvalid & _)".
    iPoseProof (IH with "Hrest") as "(%HrestLength & Hrest)".
    iSplit.
    + iPureIntro.
      cbn. rewrite app_length.
      unfold writeSuccessAccessEntryValid in Hvalid.
      destruct Hvalid as (HentryLength & _).
      lia.
    + cbn [writeSuccessAccessEntriesOwn].
      iFrame.
      done.
Qed.

Lemma write_success_transactions_151d0_to_scratch
    `{!islaG Sigma}
    (sp : bv 64)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
  (match WriteSuccessTransactionsSpec.writeSuccessTransactionTo transaction
   with
   | Some _ =>
       (bv_unsigned sp + 1744) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 265 ∗
       (bv_unsigned sp + 1752) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 273 ∗
       (bv_unsigned sp + 1760) ↦ₘ
         bv_extract 0 32
           (bv_sign_extend 64
             (bv_extract 0 32
               (bv_or
                 (bv_or
                   (bv_zero_extend 64
                      (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
                         transaction 284) ≪ 24)
                   (bv_zero_extend 64
                      (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
                         transaction 283) ≪ 16))
                 (bv_or
                   (bv_zero_extend 64
                      (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
                         transaction 282) ≪ 8)
                   (bv_zero_extend 64
                      (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
                         transaction 281)))))) ∗
       (bv_unsigned sp + 1764) ↦ₘ? 132
   | None =>
       (bv_unsigned sp + 1744) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 264 ∗
       (bv_unsigned sp + 1745) ↦ₘ? 151
   end) -∗
  (bv_unsigned sp + 1744) ↦ₘ? 40.
Proof.
  iIntros "Hto".
  destruct (WriteSuccessTransactionsSpec.writeSuccessTransactionTo transaction)
    as [address|] eqn:HtoCase.
  - iDestruct "Hto" as
      "(Hword265 & Hword273 & Hword284 & HtoRest)".
    iAssert ((bv_unsigned sp + 1744) ↦ₘ? 8)%I
      with "[Hword265]" as "Hto8_0".
    { iApply (mem_mapsto_mapsto_to_uninit _ _ 64 with "Hword265"). }
    iAssert ((bv_unsigned sp + 1752) ↦ₘ? 8)%I
      with "[Hword273]" as "Hto8_1".
    { iApply (mem_mapsto_mapsto_to_uninit _ _ 64 with "Hword273"). }
    iAssert ((bv_unsigned sp + 1760) ↦ₘ? 4)%I
      with "[Hword284]" as "Hto4".
    { iApply (mem_mapsto_mapsto_to_uninit _ _ 32 with "Hword284"). }
    iDestruct (mem_mapsto_uninit_split 20 with "HtoRest") as
      "[Hto20 HtoRest]"; [lia|].
    have Hto8Address :
        (bv_unsigned sp + 1744 + 8 = bv_unsigned sp + 1752)%Z by lia.
    iEval (rewrite <- Hto8Address) in "Hto8_1".
    have Hto20Address :
        (bv_unsigned sp + 1760 + 4 = bv_unsigned sp + 1764)%Z by lia.
    iEval (rewrite <- Hto20Address) in "Hto20".
    iAssert ((bv_unsigned sp + 1744) ↦ₘ? 16)%I
      with "[Hto8_0 Hto8_1]" as "Hto16".
    { iApply (mem_mapsto_uninit_combine 8 with
        "[Hto8_0] [Hto8_1]"); [lia|iExact "Hto8_0"|iExact "Hto8_1"]. }
    iAssert ((bv_unsigned sp + 1760) ↦ₘ? 24)%I
      with "[Hto4 Hto20]" as "Hto24".
    { iApply (mem_mapsto_uninit_combine 4 with
        "[Hto4] [Hto20]"); [lia|iExact "Hto4"|iExact "Hto20"]. }
    have Hto24Address :
        (bv_unsigned sp + 1744 + 16 = bv_unsigned sp + 1760)%Z by lia.
    iEval (rewrite <- Hto24Address) in "Hto24".
    iApply (mem_mapsto_uninit_combine 16 with
      "[Hto16] [Hto24]"); [lia|iExact "Hto16"|iExact "Hto24"].
  - iDestruct "Hto" as "(Hbyte & HtoRest)".
    iAssert ((bv_unsigned sp + 1744) ↦ₘ? 1)%I
      with "[Hbyte]" as "Hto1".
    { iApply (mem_mapsto_mapsto_to_uninit _ _ 8 with "Hbyte"). }
    iDestruct (mem_mapsto_uninit_split 39 with "HtoRest") as
      "[Hto39 HtoRest]"; [lia|].
    have Hto39Address :
        (bv_unsigned sp + 1744 + 1 = bv_unsigned sp + 1745)%Z by lia.
    iEval (rewrite <- Hto39Address) in "Hto39".
    iApply (mem_mapsto_uninit_combine 1 with
      "[Hto1] [Hto39]"); [lia|iExact "Hto1"|iExact "Hto39"].
Qed.

Lemma write_success_transactions_151d0_empty_array
    `{!islaG Sigma} (a : Z) :
  ⌜(0 <= a <= 2 ^ 64)%Z⌝ -∗
  (a ↦ₘ∗ ([] : list (bv 8)))%I.
Proof.
  iIntros "%Ha".
  rewrite mem_mapsto_array_eq /mem_mapsto_array_def.
  iExists 1%N.
  iSplit; [iPureIntro; lia|].
  iSplit; [iPureIntro; cbn; lia|].
  done.
Qed.

Lemma write_success_transactions_151d0_storage_scratch
    `{!islaG Sigma} (sp : bv 64) :
  (bv_unsigned sp + 1680) ↦ₘ? 64 -∗
  writeSuccessStorageKeysScratch sp.
Proof.
  iIntros "Hstorage".
  rewrite /writeSuccessStorageKeysScratch.
  iDestruct (mem_mapsto_uninit_split 32 with "Hstorage") as
    "[HstoragePrefix Hstorage32]"; [lia|].
  have HstorageAddress :
      (bv_unsigned sp + 1680 + 32 = bv_unsigned sp + 1712)%Z by lia.
  iEval (rewrite HstorageAddress) in "Hstorage32".
  iDestruct (mem_mapsto_uninit_split 8 with "Hstorage32") as
    "[H1712 HstorageRest]"; [lia|].
  have H1720Address :
      (bv_unsigned sp + 1712 + 8 = bv_unsigned sp + 1720)%Z by lia.
  iEval (rewrite H1720Address) in "HstorageRest".
  iDestruct (mem_mapsto_uninit_split 8 with "HstorageRest") as
    "[H1720 HstorageRest]"; [lia|].
  have H1728Address :
      (bv_unsigned sp + 1720 + 8 = bv_unsigned sp + 1728)%Z by lia.
  iEval (rewrite H1728Address) in "HstorageRest".
  iDestruct (mem_mapsto_uninit_split 8 with "HstorageRest") as
    "[H1728 HstorageTail]"; [lia|].
  have H1736Address :
      (bv_unsigned sp + 1728 + 8 = bv_unsigned sp + 1736)%Z by lia.
  iEval (rewrite H1736Address) in "HstorageTail".
  iDestruct (mem_mapsto_uninit_to_mapsto with "H1712") as
    (n0 word0 Hn0) "H1712".
  iDestruct (mem_mapsto_uninit_to_mapsto with "H1720") as
    (n1 word1 Hn1) "H1720".
  iDestruct (mem_mapsto_uninit_to_mapsto with "H1728") as
    (n2 word2 Hn2) "H1728".
  iDestruct (mem_mapsto_uninit_to_mapsto with "HstorageTail") as
    (n3 word3 Hn3) "H1736".
  cbn in Hn0, Hn1, Hn2, Hn3.
  subst n0 n1 n2 n3.
  iExists word0, word1, word2, word3.
  iFrame.
Qed.
