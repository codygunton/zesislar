Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.NatBounds.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
 WriteSuccessNativeCode WriteSuccessTransactionsSpec WriteSuccessExactTransactionsSpec
 WriteSuccessExactTransactionsGasLoads
 WriteSuccessExactTransactionsLiveSpec WriteSuccessExactTransactionsLiveCurrentRowFacts
 WriteSuccessExactTransactionsLiveNonemptyCountHandoff
 WriteSuccessExactTransactionsLiveZeroBlobBridge
 WriteSuccessExactTransactionsLiveBlobFieldGuard
 WriteSuccessExactTransactionsSourceSuffixModel
 WriteSuccessExactTransactionsBlobTailModel
 WriteSuccessExactTransactionsBlobCountTailModel
 WriteSuccessExactBlobHashesModel
 WriteSuccessExactAuthorizationsModel
 WriteSuccessExactTransactionsChainWordImage.

Lemma transactions_live_nonempty_field_handoff `{!islaG Sigma} `{!threadG}
 sp base transactions processed transaction rest bytes tail row authRest (P : iProp Sigma) :
 writeSuccessTransactionAuthorizations transaction = row :: authRest ->
 transactionLoopSourceFacts sp base transactions processed (transaction :: rest) bytes ->
 Forall writeSuccessTransactionValid transactions ->
 writeSuccessCompleteNativeCode -∗
 □ instr_pre 0x15584 (transactionLiveNonemptyCountEntry sp base transactions
   processed transaction rest bytes tail row authRest P) -∗
 □ instr_pre 0x153d0 (transactionLiveCurrentFieldEntry sp base transactions
   processed transaction rest bytes tail P).
Proof.
 intros Hrows Hfacts Hall.
 destruct (transactions_live_current_row_facts sp base transactions processed
   transaction rest bytes Hfacts Hall) as
   (Hprocessed & Hvalid & Hrow & HblobLength & HblobBound).
 have HvalidCopy := Hvalid.
 destruct HvalidCopy as
  (Hsize & Htype & Hchain & Hnonce & Hgas & Hfee & Hlimit & Hto &
   Hvalue & HdataPointer & HdataLength & HaccessPointer & HaccessCount &
   HaccessBytes & HblobPointer & HblobCount & Hhashes & HblobFee &
   HauthPointer & HauthCount & HauthRows & HV & HR & HS).
 have HfactsCopy := Hfacts.
 destruct HfactsCopy as
  (Hrelation0 & Hbytes & _ & _ & _ & HstackLow & _ & _).
 have HblobPointerRow :
   transactionRowWord bytes (288 * length processed) 224 =
   writeSuccessTransactionBlobPointer transaction.
 { rewrite Hrow; [exact HblobPointer | lia]. }
 have HauthPointerRow :
   transactionRowWord bytes (288 * length processed) 240 =
   writeSuccessTransactionAuthorizationPointer transaction.
 { rewrite Hrow; [exact HauthPointer | lia]. }
 have HblobCountRow :
   transactionRowWord bytes (288 * length processed) 232 =
   Z_to_bv 64 (Z.of_nat (length (writeSuccessTransactionBlobHashes transaction))).
 { apply bv_eq. rewrite Z_to_bv_small.
   - rewrite Hrow; [exact HblobCount | lia].
   - split; first lia. exact HblobBound. }
 have Hsuffix := transactions_source_suffix_model sp processed transaction rest
   (writeSuccessExactTransactionsEvents sp rest tail) Hprocessed Hvalid.
 rewrite -Hrelation0 -Hbytes in Hsuffix.
 have HblobTail := transactions_exact_blob_tail sp transaction
   (writeSuccessExactTransactionsEvents sp rest tail) Hhashes.
 rewrite Hrows in Hsuffix.
 have Hevents :
   writeSuccessExactBlobHashesEvents sp 0
     (length (writeSuccessTransactionBlobHashes transaction))
     (writeSuccessTransactionBlobBytes transaction)
     (transactionSourceAfterBlobEvents sp bytes (288 * length processed)
       (row :: authRest) (writeSuccessExactTransactionsEvents sp rest tail)) =
   writeSuccessExactTransactionAfterBlobCountEvents sp transaction
     (writeSuccessExactTransactionsEvents sp rest tail).
 { rewrite HblobTail Hsuffix. reflexivity. }
 unfold transactionSourceAfterBlobEvents in Hevents.
 iIntros "#Hcode #Hcount".
 unfold transactionLiveNonemptyCountEntry, transactionLiveCurrentFieldEntry.
 iApply (transactions_live_blob_field_guard sp base transactions processed
   transaction rest bytes (writeSuccessTransactionData transaction)
   (writeSuccessTransactionAccessBytes transaction)
   (transactionChainWordImage
     (transactionRowWord bytes (288 * length processed) 160)
     (transactionRowWord bytes (288 * length processed) 168))
   (writeSuccessTransactionAccessEntries transaction)
   (writeSuccessTransactionBlobBytes transaction)
   (writeSuccessTransactionAuthorizationBytes transaction)
   (writeSuccessExactAuthorizationEvents sp (row :: authRest)
     (transactionSourceSignatureEvents sp bytes (288 * length processed)
       (writeSuccessExactTransactionsEvents sp rest tail)))
   (writeSuccessExactTransactionAfterBlobCountEvents sp transaction
     (writeSuccessExactTransactionsEvents sp rest tail)) P
   ltac:(reflexivity) ltac:(reflexivity) HblobLength HblobCountRow HblobBound
   HblobPointerRow HauthPointerRow ltac:(lia) Hevents
   with "Hcode Hcount").
Qed.
Print Assumptions transactions_live_nonempty_field_handoff.
