Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.UninitWords.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
 WriteSuccessTransactionsSpec WriteSuccessExactTransactionsSpec WriteSuccessStorageKeysSpec WriteSuccessAccessListsSpec
 WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsFlagLoads
 WriteSuccessExactBlobHashesAuthorizationEntry
 WriteSuccessExactTransactionsSourceFieldLayout WriteSuccessExactTransactionsSourceBlobFeeFrame
 WriteSuccessExactTransactionsSourceAuthorizationSpec
 WriteSuccessExactTransactionsSourceAuthorizationLiveFrame
 WriteSuccessExactTransactionsLiveSpec WriteSuccessExactTransactionsLiveBackEdgeHandoff
 WriteSuccessExactTransactionsBackEdge WriteSuccessExactTransactionsLayout.
Lemma transactions_source_signature_back_edge_entry `{!islaG Sigma} `{!threadG}
 sp base transactions processed transaction rest bytes chainBytes tail (P : iProp Sigma) :
 length chainBytes = 16%nat ->
 transactionSourceAuthorizationExit sp base bytes (length processed) (288 * length processed)
  (writeSuccessTransactionData transaction) (writeSuccessTransactionAccessBytes transaction) chainBytes
  (writeSuccessTransactionAccessEntries transaction) (writeSuccessTransactionBlobBytes transaction)
  (writeSuccessTransactionAuthorizationBytes transaction)
  (writeSuccessExactTransactionsEvents sp rest tail)
  (transactionLiveAuthorizationRemainder sp base transactions processed transaction rest bytes P) -∗
 instr_pre 0x14f04 (transactionBackEdgePost sp (Z_to_bv 64 (Z.of_nat (length processed)))
  (Z_to_bv 64 (Z.of_nat (length transactions)))
  (transactionLiveBackEdgeFrame sp base transactions processed transaction rest bytes tail P)) -∗
 transactionBackEdgeEntry sp (Z_to_bv 64 (Z.of_nat (length processed)))
  (Z_to_bv 64 (Z.of_nat (length transactions)))
  (transactionLiveBackEdgeFrame sp base transactions processed transaction rest bytes tail P).
Proof.
 intros HchainLength.
 iIntros "Hexit Hnext".
 iEval (unfold transactionSourceAuthorizationExit) in "Hexit".
 iDestruct "Hexit" as "(Hsys & Hsp & HcallRegs & H18 & Hupper & Hmmio & Htrace & H144 & H152 & H160 & Hframe & _)".
 iEval (unfold transactionSourceBlobFeeRetained) in "Hframe".
 iDestruct "Hframe" as (pointer storedIndex) "Hframe".
 iDestruct "Hframe" as
  "(H19 & H22 & Hregs & Hblob & HblobCount & Haccess & Hentries & HaccessBase & HaccessCount & HaccessIndex & Hcopy & Hkeys & Hlower & Hrec0 & Hrec1 & Hrec2 & Htag & Hvalue & Hdata & Hchain & Hmemory & _)".
 iEval (unfold transactionFieldSourceFeeRest) in "Hmemory".
 iDestruct "Hmemory" as "(Hbytes & Hbase & Hindex & Hmemory)".
 iDestruct "Hmemory" as
  "(H168 & H176 & H184 & H192 & H200 & H208 & H216 & H224 & H232 & H240 & H1660 & H1680 & H1784 & %HdataBounds & %HaccessBounds & Hremaining & _)".
 iEval (unfold transactionLiveAuthorizationRemainder) in "Hremaining".
 iDestruct "Hremaining" as "(Hauth & Htotal & Hprocessed & Hrest & %Hvalid & %Hfacts & HP & _)".
 iDestruct (exact_transactions_own_valid with "Hprocessed") as "(Hprocessed & %HprocessedValid & _)".
 have Hrelation := Hfacts.
 destruct Hrelation as (Hrelation & HbytesModel & _).
 have Hrow : forall offset, (offset + 8 <= 288)%nat -> transactionRowWord bytes (288 * length processed) offset = writeSuccessTransactionWord transaction offset.
 {
 intros offset Hoffset.
 rewrite HbytesModel Hrelation.
 apply exact_transaction_row_word; assumption.
 }
 zesu_open_resource_groups.
 have HdataPointer : transactionRowWord bytes (288 * length processed) 192 = writeSuccessTransactionDataPointer transaction.
 {
 rewrite Hrow; last lia.
 unfold writeSuccessTransactionValid in Hvalid.
 tauto.
 }
 have HaccessPointer : transactionRowWord bytes (288 * length processed) 208 = writeSuccessTransactionAccessPointer transaction.
 {
 rewrite Hrow; last lia.
 unfold writeSuccessTransactionValid in Hvalid.
 tauto.
 }
 have HblobPointer : transactionRowWord bytes (288 * length processed) 224 = writeSuccessTransactionBlobPointer transaction.
 {
 rewrite Hrow; last lia.
 unfold writeSuccessTransactionValid in Hvalid.
 tauto.
 }
 have HauthPointer : transactionRowWord bytes (288 * length processed) 240 = writeSuccessTransactionAuthorizationPointer transaction.
 {
 rewrite Hrow; last lia.
 unfold writeSuccessTransactionValid in Hvalid.
 tauto.
 }
 iEval (rewrite HdataPointer) in "Hdata".
 iEval (rewrite HaccessPointer) in "Haccess".
 iEval (rewrite HblobPointer) in "Hblob".
 iEval (rewrite HauthPointer) in "Hauth".
 rewrite HdataPointer in HdataBounds.
 rewrite HaccessPointer in HaccessBounds.
 iAssert (writeSuccessByteArrayOwn (writeSuccessTransactionDataPointer transaction) (writeSuccessTransactionData transaction)) with "[Hdata]" as "HdataOwn".
 {
 destruct (writeSuccessTransactionData transaction) as [|head dataTail] eqn:HdataCase.
 -
 done.
 -
 have Hbounds := HdataBounds ltac:(discriminate).
 cbn [writeSuccessByteArrayOwn].
 iFrame "Hdata".
 zesu_finish_pure_resources.
 }
 iAssert (writeSuccessByteArrayOwn (writeSuccessTransactionAccessPointer transaction) (writeSuccessTransactionAccessBytes transaction)) with "[Haccess]" as "HaccessOwn".
 {
 destruct (writeSuccessTransactionAccessBytes transaction) as [|head accessTail] eqn:HaccessCase.
 -
 done.
 -
 have Hbounds := HaccessBounds ltac:(discriminate).
 cbn [writeSuccessByteArrayOwn].
 iFrame "Haccess".
 zesu_finish_pure_resources.
 }
 iAssert (writeSuccessTransactionOwn transaction) with "[HdataOwn HaccessOwn Hentries Hblob Hauth]" as "Htransaction".
 {
 unfold writeSuccessTransactionOwn.
 iFrame "HdataOwn HaccessOwn Hentries Hblob Hauth".
 done.
 }
 iAssert (writeSuccessTransactionsOwn transactions) with "[Hprocessed Htransaction Hrest]" as "Htransactions".
 {
 rewrite Hrelation.
 rewrite /writeSuccessTransactionsOwn.
 fold writeSuccessTransactionsOwn.
 rewrite WriteSuccessExactTransactionsOwnership.transactions_own_app.
 cbn [writeSuccessTransactionsOwn].
 iFrame "Hprocessed Htransaction Hrest".
 }
 have HboundCopy := Hfacts.
 destruct HboundCopy as (_ & _ & _ & _ & Halign & Hlow & Hhigh & _).
 iEval (unfold writeSuccessStorageKeysScratch) in "Hkeys".
 zesu_open_resource_groups.
 unfold transactionBackEdgeEntry, transactionLiveBackEdgeFrame.
 iFrame "Hsys Hsp Htotal Hindex Hbytes Htransactions Hbase Hmmio Htrace HP Hnext".
 zesu_open_bits_registers.
 iPoseProof (ArrayForget.byte_array_forget with "Hchain") as "HchainUninit".
 iEval (rewrite HchainLength) in "HchainUninit".
 have HchainAddress : bv_unsigned (sp + BV 64 1664)%bv = (bv_unsigned sp + 1664)%Z by bv_solve.
 iEval (rewrite HchainAddress) in "HchainUninit".
 iDestruct "Hkeys" as (word0 word1 word2 word3) "(Hkey0 & Hkey1 & Hkey2 & Hkey3 & _)".
 zesu_run.
Qed.
Print Assumptions transactions_source_signature_back_edge_entry.
