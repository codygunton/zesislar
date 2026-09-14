Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.UninitWords.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsFlagLoads
  WriteSuccessExactTransactionsSourceFieldLayout
  WriteSuccessExactAccessListsReturnLoopEntry
  WriteSuccessExactTransactionsDataAccessEntry
  WriteSuccessExactBlobHashesAuthorizationEntry
  WriteSuccessTransactionsSpec WriteSuccessStorageKeysSpec WriteSuccessAccessListsSpec
  WriteSuccessBlobHashesSpec WriteSuccessExactAuthorizationsPrefix
  WriteSuccessExactAuthorizationsCount WriteSuccessExactTransactionsMaxBlobFeeCount
  WriteSuccessExactEncoderU128 WriteSuccessObservation WriteSuccessOutputSemantic.

From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSourceBlobHeaderHandoff
  WriteSuccessExactTransactionsSourceBlobFeeFrame.

Lemma transactions_source_blob_fee_entry `{!islaG Sigma} `{!threadG}
    sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes
    total tail (Q : iProp Sigma) :
  (0 < total)%nat ->
  length blobBytes = (32 * total)%nat ->
  (mapRamBase defaultMap) <= bv_unsigned sp - 32 ->
  writeSuccessBlobHashesLoopExit sp (bv_unsigned (transactionRowWord bytes index 224))
    total blobBytes
    (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
      (writeSuccessU128WordsPayload (transactionRowWord bytes index 80) (transactionRowWord bytes index 88))
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64
          (bv_unsigned (transactionRowWord bytes index 248)))) tail))
    (transactionSourceBlobRetained sp base bytes processed index dataBytes accessBytes
      chainBytes entries blobBytes Q) -∗
  instr_pre 0x15584 (authorizationCountPost sp (transactionRowWord bytes index 248) tail
    (maxBlobFeeCountFrame sp (transactionRowWord bytes index 80) (transactionRowWord bytes index 88)
      (transactionSourceBlobFeeRetained sp base bytes processed index dataBytes accessBytes
        chainBytes entries blobBytes Q))) -∗
  ∃ oldra old5 : bv 64,
    authorizationPrefixEntry sp (transactionRowWord bytes index 80) (transactionRowWord bytes index 88)
      (transactionRowWord bytes index 248) oldra old5 tail
      (transactionSourceBlobFeeRetained sp base bytes processed index dataBytes accessBytes
        chainBytes entries blobBytes Q).
Proof.
  intros Hpositive Hlength Hlower.
  unfold writeSuccessBlobHashesLoopExit.
  iIntros "Hexit Hnext". iDestruct "Hexit" as (pointer)
    "(Hsys & Hregs & Hsp & Hptr & H22 & Hblob & Hscratch & Hmmio & Htrace & Hcaller & %Hpointer & _)".
  iAssert ((bv_unsigned sp + 1680) ↦ₘ? 32)%I with "[Hscratch]" as "Hscratch".
  { iDestruct "Hscratch" as (a b c d) "Hscratch".
    zesu_open_resource_groups. zesu_run. }
  iEval (unfold transactionSourceBlobRetained, accessReturnRuntimeBounds,
    transactionAccessRetainedMemory) in "Hcaller".
  iDestruct "Hcaller" as (storedIndex)
    "(HblobCount & Haccess & Hown & HaccessBase & HaccessCount & HaccessIndex &
      Hcopied & Hkeys & Hlower16 & (%Halign & %Hlow & %Hhigh &
      (Hsrc0 & Hsrc1 & Hsrc2 & Htag & Hvalue & Hdata & Hlower32 &
       (Hchain & Hmemory & _) & _) & _) & %HblobLow & %HblobHigh & _)".
  iPoseProof ("Hmemory" with "Hscratch") as "Hmemory".
  iPoseProof (transactions_source_fee_frame with "Hmemory") as
    "(HfeeHigh & HfeeLow & Hcount & Hmemory)".
  iDestruct (reg_col_lookup writeSuccessBlobHashesOtherRegShapes 0%nat (KindReg "x1", BitsShape 64)
    ltac:(vm_compute; reflexivity) with "Hregs") as (v0 Hv0) "(Hx1 & Hregs)".
  iDestruct (reg_col_lookup (list_delete 0%nat writeSuccessBlobHashesOtherRegShapes) 2%nat (KindReg "x5", BitsShape 64)
    ltac:(vm_compute; reflexivity) with "Hregs") as (v1 Hv1) "(Hx5 & Hregs)".
  iDestruct (reg_col_lookup (list_delete 2%nat (list_delete 0%nat writeSuccessBlobHashesOtherRegShapes)) 6%nat (KindReg "x10", BitsShape 64)
    ltac:(vm_compute; reflexivity) with "Hregs") as (v2 Hv2) "(Hx10 & Hregs)".
  iDestruct (reg_col_lookup (list_delete 6%nat (list_delete 2%nat (list_delete 0%nat writeSuccessBlobHashesOtherRegShapes))) 6%nat (KindReg "x11", BitsShape 64)
    ltac:(vm_compute; reflexivity) with "Hregs") as (v3 Hv3) "(Hx11 & Hregs)".
  iDestruct (reg_col_lookup (list_delete 6%nat (list_delete 6%nat (list_delete 2%nat (list_delete 0%nat writeSuccessBlobHashesOtherRegShapes)))) 12%nat (KindReg "x18", BitsShape 64)
    ltac:(vm_compute; reflexivity) with "Hregs") as (v4 Hv4) "(Hx18 & Hregs)".
  destruct (valu_has_bits_shape _ _ Hv0) as [oldra ->].
  destruct (valu_has_bits_shape _ _ Hv1) as [old5 ->].
  iExists oldra, old5.
  destruct blobBytes as [|byte blobBytes]; first (simpl in Hlength; lia).
  unfold authorizationPrefixEntry, transactionSourceBlobFeeRetained.
  iDestruct "Hkeys" as (key0 key1 key2 key3) "Hkeys".
  iEval (unfold transactionFieldSourceFeeRest) in "Hmemory".
  zesu_open_resource_groups.
  zesu_run.
Qed.
Print Assumptions transactions_source_blob_fee_entry.
