Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.NatBounds.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
 WriteSuccessNativeCode WriteSuccessTransactionsSpec WriteSuccessExactTransactionsSpec
 WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsLiveSpec
 WriteSuccessExactTransactionsLiveCurrentRowFacts
 WriteSuccessExactTransactionsLiveAuthorizationCountFacts
 WriteSuccessExactTransactionsLiveSignatureGuard
 WriteSuccessExactTransactionsLiveCompositionFrames
 WriteSuccessExactTransactionsSourceAuthorizationFacts
 WriteSuccessExactTransactionsSourceAuthorizationCountContinuation
 WriteSuccessExactTransactionsSourceAuthorizationLiveFrame
 WriteSuccessExactTransactionsSourceSuffixModel
 WriteSuccessExactTransactionsSourceBlobFeeFrame
 WriteSuccessExactTransactionsMaxBlobFeeCount
 WriteSuccessExactAuthorizationsCount
 WriteSuccessExactAuthorizationsModel
 WriteSuccessExactTransactionsChainWordImage.

Definition transactionLiveNonemptyCountEntry `{!islaG Sigma} `{!threadG}
 sp base transactions processed transaction rest bytes tail row authRest (P : iProp Sigma)
   : iProp Sigma :=
 authorizationCountPost sp
   (transactionRowWord bytes (288 * length processed) 248)
   (writeSuccessExactAuthorizationEvents sp (row :: authRest)
     (transactionSourceSignatureEvents sp bytes (288 * length processed)
       (writeSuccessExactTransactionsEvents sp rest tail)))
   (maxBlobFeeCountFrame sp
     (transactionRowWord bytes (288 * length processed) 80)
     (transactionRowWord bytes (288 * length processed) 88)
     (transactionSourceBlobFeeRetained sp base bytes (length processed)
       (288 * length processed) (writeSuccessTransactionData transaction)
       (writeSuccessTransactionAccessBytes transaction)
       (transactionChainWordImage
         (transactionRowWord bytes (288 * length processed) 160)
         (transactionRowWord bytes (288 * length processed) 168))
       (writeSuccessTransactionAccessEntries transaction)
       (writeSuccessTransactionBlobBytes transaction)
       (writeSuccessByteArrayOwn
          (transactionRowWord bytes (288 * length processed) 240)
          (writeSuccessTransactionAuthorizationBytes transaction) ∗
        transactionLiveAuthorizationRemainder sp base transactions processed
          transaction rest bytes P)%I)).

Global Instance : LithiumUnfold (@transactionLiveNonemptyCountEntry) := I.

Lemma transactions_live_nonempty_count_handoff `{!islaG Sigma} `{!threadG}
 sp base transactions processed transaction rest bytes tail row authRest (P : iProp Sigma) :
 writeSuccessTransactionAuthorizations transaction = row :: authRest ->
 transactionLoopSourceFacts sp base transactions processed (transaction :: rest) bytes ->
 Forall writeSuccessTransactionValid transactions ->
 writeSuccessCompleteNativeCode -∗
 □ instr_pre 0x14f04 (transactionLiveLoopState sp base transactions
   (processed ++ [transaction]) rest bytes tail P) -∗
 transactionLiveLoopState sp base transactions processed (transaction :: rest) bytes tail P -∗
 transactionLiveLoopState sp base transactions processed (transaction :: rest) bytes tail P ∗
 □ instr_pre 0x15584 (transactionLiveNonemptyCountEntry sp base transactions
   processed transaction rest bytes tail row authRest P).
Proof.
 intros Hrows Hfacts Hall.
 destruct (transactions_live_current_row_facts sp base transactions processed
   transaction rest bytes Hfacts Hall) as
   (Hprocessed & Hvalid & Hrow & _ & _).
 have HvalidCopy := Hvalid.
 destruct HvalidCopy as
  (Hsize & Htype & Hchain & Hnonce & Hgas & Hfee & Hlimit & Hto &
   Hvalue & HdataPointer & HdataLength & HaccessPointer & HaccessCount &
   HaccessBytes & HblobPointer & HblobCount & Hhashes & HblobFee &
   HauthPointer & HauthCount & HauthRows & HV & HR & HS).
 have HfactsCopy := Hfacts.
 destruct HfactsCopy as
  (Hrelation0 & Hbytes & _ & _ & Halign & HstackLow & HstackHigh & _).
 have HauthPointerRow :
   transactionRowWord bytes (288 * length processed) 240 =
   writeSuccessTransactionAuthorizationPointer transaction.
 { rewrite Hrow; [exact HauthPointer | lia]. }
 have HauthFacts := transactions_live_authorization_count_facts transaction bytes
   (288 * length processed) Hvalid ltac:(apply Hrow; lia).
 destruct HauthFacts as (HauthCountWord & _ & _).
 have HrowLength : length row = 144%nat.
 { rewrite Hrows in HauthRows. exact (Forall_inv HauthRows). }
 have HauthNonempty : writeSuccessTransactionAuthorizationBytes transaction <> [].
 { unfold writeSuccessTransactionAuthorizationBytes. rewrite Hrows. cbn.
   destruct row as [|byte row']; [cbn in HrowLength; lia | discriminate]. }
 have HauthCountRow :
   transactionRowWord bytes (288 * length processed) 248 =
     Z_to_bv 64 (Z.of_nat (S (length authRest))).
 { rewrite HauthCountWord Hrows. reflexivity. }
 iIntros "#Hcode #Hnext Hstate".
 iDestruct (transactions_live_authorization_bounds sp base transactions processed
   transaction rest bytes tail P HauthNonempty with "Hstate")
   as "(%HauthLow & %HauthHigh & Hstate)".
 have Hinitial := transactions_source_authorization_initial_facts sp transactions
   processed transaction rest bytes row authRest Hprocessed Hvalid Hrelation0 Hbytes Hrows
   Halign HstackLow HstackHigh
   ltac:(rewrite HauthPointerRow; exact HauthLow)
   ltac:(rewrite HauthPointerRow; exact HauthHigh).
 destruct Hinitial as [HauthorizationFacts _].
 iPoseProof (transactions_live_signature_guard sp base transactions processed
   transaction rest bytes tail P Hfacts with "Hcode Hnext") as "#Hsignature".
 iPoseProof (transactions_source_authorization_count_continuation sp base bytes
   (length processed) (288 * length processed)
   (writeSuccessTransactionData transaction)
   (writeSuccessTransactionAccessBytes transaction)
   (transactionChainWordImage
     (transactionRowWord bytes (288 * length processed) 160)
     (transactionRowWord bytes (288 * length processed) 168))
   (writeSuccessTransactionAccessEntries transaction)
   (writeSuccessTransactionBlobBytes transaction)
   (writeSuccessTransactionAuthorizationBytes transaction) row authRest
   (transactionSourceSignatureEvents sp bytes (288 * length processed)
     (writeSuccessExactTransactionsEvents sp rest tail))
   (transactionLiveAuthorizationRemainder sp base transactions processed
     transaction rest bytes P)
   HauthorizationFacts HauthCountRow with "Hcode Hsignature") as "#Hcount".
 iFrame "Hstate". unfold transactionLiveNonemptyCountEntry. iExact "Hcount".
Qed.
Print Assumptions transactions_live_nonempty_count_handoff.
