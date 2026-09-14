Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ByteArrays.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsTypeOutput WriteSuccessExactTransactionsTypeSourceEntry
  WriteSuccessExactTransactionsSourceLayout WriteSuccessExactTransactionsChainSomeCaller
  WriteSuccessExactTransactionsSourceFieldLayout WriteSuccessExactTransactionsChainWordImage
  WriteSuccessExactTransactionsByteArrayOwn WriteSuccessExactTransactionsGasRecipientSource
  WriteSuccessExactTransactionsNestedSourceEntry WriteSuccessExactTransactionsWideSignatureSuffixEntry
  WriteSuccessExactTransactionsValueMiddleWordsEntry WriteSuccessExactTransactionsRecipientTagShiftEntry
  WriteSuccessExactTransactionsSignatureFieldEntry WriteSuccessExactTransactionsGasSignatureEntry
  WriteSuccessOutputSemantic WriteSuccessExactBooleanSpec WriteSuccessObservation
  WriteSuccessExactTransactionsGasLoads WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Automation.ByteScratch.
Require Import ZesuSsz.Automation.UninitWords.
Require Import ZesuSsz.Automation.NatPowerGoals.

Lemma transactions_type_to_chain_some `{!islaG Sigma} `{!threadG}
    (sp row chain tagWord : bv 64) base bytes processed index kind
    dataBytes accessBytes entries tail (Q : iProp Sigma) :
  bv_extract 0 8 tagWord <> BV 8 0 ->
  bv_unsigned sp `mod` 16 = 0 ->
  (mapRamBase defaultMap) <= bv_unsigned sp - 48 ->
  bv_unsigned sp + 1896 < (machineRamEnd defaultMap) ->
  transactionTypeOutputPost (sp + BV 64 1744)%bv kind
    (writeOutputEvents (sp - BV 64 25)%bv (BV 64 1)
      (writeSuccessBooleanWordPayload (BV 64 1))
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned chain))) tail))
    (transactionTypeSourceRetained sp row chain tagWord base bytes index
      (transactionSourceRetainedStack sp base processed ∗
       ((bv_unsigned sp - 48) ↦ₘ? 48 ∗
        transactionFieldSourceHeap bytes index dataBytes accessBytes entries ∗ Q ∗ True) ∗ True)%I) -∗
  transactionChainSomeCaller chain sp (BV 64 0x150f0) (sp + BV 64 1744)%bv
    (BV 64 (mapIoContextAddress defaultMap)) (transactionRecipientSourceOld6 bytes index)
    (transactionRowWord bytes index 192) (BV 64 1) (bv_extract 0 8 tagWord)
    (transactionChainWordImage chain tagWord) tail
    (transactionSourceFieldCaller sp base bytes processed index dataBytes accessBytes entries Q).
Proof.
  intros Htag HspAlign Hlow Hhigh. iStartProof. iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H1 & H5 & H10 & H11 & Hkind & Hmmio & Htrace & Hretained & _)".
  iEval (unfold transactionTypeSourceRetained) in "Hretained".
  iDestruct "Hretained" as "(H2 & Hbytes & H13 & H14 & H176 & H1648 & H1656 &
    %Hcursor & %Hlength & %HrowAlign & %HspAlign8 & %HbaseLow & %HbaseHigh &
    %HspLow & %HkindHigh & H19 & H12 & H22 & H136 & H160 & H168 & H256 & H264 & H1640 & Hregisters & _)".
  iEval (unfold transactionTypeSourceRegisters) in "Hregisters".
  iDestruct "Hregisters" as "(H16 & H7 & H28 & H17 & H6 & H29 & H30 & H27 & H18 & H20 & H31 & Hstored & _)".
  iDestruct "Hstored" as "(H15 & H208 & H184 & H192 & H200 & Hsignature & _)".
  iDestruct "Hsignature" as "(H21 & H128 & H144 & H152 & H216 & Hassembly & _)".
  iDestruct "Hassembly" as "(H120 & H1664 & H1672 & Hfields & _)".
  iDestruct "Hfields" as "(H26 & H8 & H272 & HsignatureFields & _)".
  iDestruct "HsignatureFields" as "(H224 & H232 & H240 & %HrowAlign2 & %Hlength2 & %HstackHigh & Hgas & _)".
  iDestruct "Hgas" as "(H25 & H24 & H9 & H23 & %Hlength3 & %HstackHigh2 & Hcaller & _)".
  iDestruct "Hcaller" as "(Hstack & Hcurrent & _)".
  iDestruct "Hcurrent" as "(Hlower & Hheap & HQ & _)".
  iEval (unfold transactionSourceRetainedStack) in "Hstack".
  iDestruct "Hstack" as "(H104 & H248 & H1660 & H1680 & H1745 & Hgp & _)".
  iEval (unfold transactionFieldSourceHeap) in "Hheap".
  iDestruct "Hheap" as "(HdataOwn & HaccessOwn & Hentries & %HdataLength & %Hcount & %Hencoding & %HaccessLength & %HaccessBound & _)".
  iPoseProof (transaction_byte_array_own_view with "HdataOwn") as "(Hdata & %HdataBounds & _)".
  iPoseProof (transaction_byte_array_own_view with "HaccessOwn") as "(Haccess & %HaccessBounds & _)".
  have HaccessNonempty : entries <> [] -> accessBytes <> [].
  { clear -HaccessLength; intros Hentries Hbytes; subst accessBytes;
    destruct entries; [done | cbn in HaccessLength; lia]. }
  have HaccessLow : entries <> [] ->
    (mapRamBase defaultMap) <= bv_unsigned (transactionRowWord bytes index 208).
  { intros Hentries. exact (proj1 (HaccessBounds (HaccessNonempty Hentries))). }
  have HaccessHigh : entries <> [] ->
    bv_unsigned (transactionRowWord bytes index 208) + Z.of_nat (length accessBytes) < (machineRamEnd defaultMap).
  { intros Hentries. exact (proj2 (HaccessBounds (HaccessNonempty Hentries))). }
  have HchainAddress : bv_unsigned (sp + BV 64 1664)%bv = bv_unsigned sp + 1664.
  { clear -Hlow Hhigh. bv_solve. }
  destruct (transactions_chain_word_image chain tagWord) as (HchainTag & HchainValue & HchainLength).
  iEval (replace (bv_unsigned sp + 1672) with (bv_unsigned sp + 1664 + 8)
    by (clear -sp; lia)) in "H1672".
  iPoseProof (mem_mapsto_u64_pair_to_byte_array (bv_unsigned sp + 1664) chain tagWord
    with "H1664 H1672") as "Hchain".
  iEval (fold (transactionChainWordImage chain tagWord); rewrite -HchainAddress) in "Hchain".
  iAssert (∃ _ : unit, transactionFieldSourceRetained sp base bytes processed index dataBytes accessBytes Q ∗
      (bv_unsigned sp + 1712) ↦ₘ? 32 ∗ (bv_unsigned sp + 1745) ↦ₘ? 19 ∗
      (bv_unsigned sp + 1764) ↦ₘ? 20 ∗ True)%I
    with "[Hbytes H104 H248 H144 H152 H160 H168 H176 H184 H192 H200 H208 H216 H224 H232 H240 H1660 H1680 H1745 HQ]" as "Hframe".
  { zesu_run. }
  iDestruct "Hframe" as (_) "(Hframe & Hkeys & HkindRest & Hextra & _)".
  iEval (unfold transactionFieldSourceRetained) in "Hframe".
  zesu_open_resource_groups.
  iAssert (∃ _ : unit, transactionChainSomeCaller chain sp (BV 64 0x150f0)
    (sp + BV 64 1744)%bv (BV 64 (mapIoContextAddress defaultMap)) (transactionRecipientSourceOld6 bytes index)
    (transactionRowWord bytes index 192) (BV 64 1) (bv_extract 0 8 tagWord)
    (transactionChainWordImage chain tagWord) tail
    (transactionSourceFieldCaller sp base bytes processed index dataBytes accessBytes entries Q) ∗ True)%I
    with "[-]" as "Hentry".
  { unfold transactionChainSomeCaller, optionalU64SomeExactCallerContext,
      transactionSourceFieldCaller, transactionSourceFieldCore.
    cbn [transactionRecipientSourceWord transactionRecipientSourceLast
      transactionRecipientSourceOld6 seq fmap list_fmap].
    zesu_run_nat_safe. }
  iDestruct "Hentry" as (_) "[Hentry _]". iExact "Hentry".
Qed.
Print Assumptions transactions_type_to_chain_some.
