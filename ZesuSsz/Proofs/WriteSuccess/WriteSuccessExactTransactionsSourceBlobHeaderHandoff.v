Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.Resources.
Require Import ZesuSsz.Automation.UninitWords.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessBlobHashesSpec WriteSuccessStorageKeysSpec
  WriteSuccessAccessListsSpec WriteSuccessExactBlobHashesModel
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsFlagLoads
  WriteSuccessExactTransactionsSourceFieldEvents
  WriteSuccessExactTransactionsSourceFieldLayout WriteSuccessExactTransactionsDataAccessEntry
  WriteSuccessExactAccessListsReturnCount WriteSuccessExactAccessListsReturnLoopEntry
  WriteSuccessExactAccessListsRegisterGroups WriteSuccessExactEncoderIntFramedCall
  WriteSuccessExactTransactionsSourceBlobMemoryFrame WriteSuccessExactBlobHashesHeader.

Definition transactionSourceBlobRetained `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (bytes : list (bv 8)) (processed index : nat)
    (dataBytes accessBytes chainBytes : list (bv 8)) (entries : list writeSuccessAccessEntry) (blobBytes : list (bv 8))
    (Q : iProp Sigma) : iProp Sigma :=
  (∃ storedIndex : bv 64,
   (bv_unsigned sp + 136) ↦ₘ transactionRowWord bytes index 232 ∗
   bv_unsigned (transactionRowWord bytes index 208) ↦ₘ∗ accessBytes ∗
   writeSuccessAccessEntriesOwn entries ∗
   (bv_unsigned sp + 256) ↦ₘ transactionRowWord bytes index 208 ∗
   (bv_unsigned sp + 264) ↦ₘ Z_to_bv 64 (Z.of_nat (length entries)) ∗
   (bv_unsigned sp + 272) ↦ₘ storedIndex ∗
   (bv_unsigned sp + 1744) ↦ₘ? 40 ∗ writeSuccessStorageKeysScratch sp ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   accessReturnRuntimeBounds sp
     (transactionAccessRetainedMemory sp (transactionRowByte bytes index 285)
       (transactionRecipientSourceWord bytes index 265) (transactionRecipientSourceWord bytes index 273)
       (transactionRowWord bytes index 64) (transactionRowWord bytes index 192)
       (transactionRecipientSourceLast bytes index) dataBytes
       (bv_unsigned (sp + BV 64 1664)%bv ↦ₘ∗ chainBytes ∗
        ((bv_unsigned sp + 1680) ↦ₘ? 32 -∗
          transactionFieldSourceRetained sp base bytes processed index dataBytes accessBytes Q) ∗ True)%I) ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned (transactionRowWord bytes index 224)⌝ ∗
   ⌜bv_unsigned (transactionRowWord bytes index 224) + Z.of_nat (length blobBytes) <
     (machineRamEnd defaultMap)⌝ ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSourceBlobRetained) := I.

Lemma transactions_source_blob_header_handoff `{!islaG Sigma} `{!threadG}
    sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes total tail
    (Q : iProp Sigma) :
  (0 < total)%nat ->
  length blobBytes = (32 * total)%nat ->
  transactionRowWord bytes index 232 = Z_to_bv 64 (Z.of_nat total) ->
  (Z.of_nat total < 18446744073709551616)%Z ->
  transactionSourceFieldPost sp base bytes processed index dataBytes accessBytes chainBytes entries
    (writeSuccessExactBlobHashesEvents sp 0 total blobBytes tail)
    (writeSuccessByteArrayOwn (transactionRowWord bytes index 224) blobBytes ∗ Q)%I -∗
  instr_pre 0x15564 (writeSuccessBlobHashesLoopExit sp
    (bv_unsigned (transactionRowWord bytes index 224)) total blobBytes tail
    (transactionSourceBlobRetained sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes Q)) -∗
  blobHeaderEntry sp (transactionRowWord bytes index 224)
    (bv_unsigned (transactionRowWord bytes index 224)) total blobBytes tail
    (transactionSourceBlobRetained sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes Q).
Proof.
  intros Hpositive Hlength Hcount Hbound.
  iStartProof. iIntros "Hpost Hnext".
  iEval (unfold transactionSourceFieldPost, accessReturnCountPost, encoderIntExactFramedPost,
    accessReturnCountFrame, accessReturnLoopFrame, accessReturnRuntimeBounds,
    transactionAccessRetainedMemory) in "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hlower & Hmmio & Htrace & (H22 & Hsaved & Hloop & _) & _)".
  iDestruct "Hloop" as (storedIndex old27)
    "(Htmp & Hother & H19 & H27 & Haccess & Hown & HaccessBase & HaccessCount & HaccessIndex &
      Hcopied & Hkeys & (%Halign & %Hlow & %Hhigh &
      (Hsrc0 & Hsrc1 & Hsrc2 & Htag & Hvalue & Hdata & Hlower32 &
       (Hchain & Hmemory & _) & _) & _) & _)".
  iPoseProof (transactions_source_blob_memory_frame with "Hmemory") as "(Hscratch & Hblob & Hmemory)".
  destruct blobBytes as [|byte blobBytes]; first (simpl in Hlength; lia).
  iEval (unfold writeSuccessByteArrayOwn) in "Hblob".
  iDestruct "Hblob" as "(Hblob & %HblobLow & %HblobHigh & _)".
  iEval (rewrite Hcount) in "H22".
  iEval (unfold accessRegisterGroup) in "Htmp Hother".
  iEval (unfold writeSuccessStorageKeysScratch) in "Hkeys".
  iDestruct "Hkeys" as (a b c d) "Hkeys".
  unfold blobHeaderEntry, transactionSourceBlobRetained.
  zesu_open_resource_groups.
  zesu_run.
Qed.
Print Assumptions transactions_source_blob_header_handoff.
