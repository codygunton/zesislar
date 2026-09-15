Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
 WriteSuccessNativeCode WriteSuccessTransactionsSpec WriteSuccessExactTransactionsSpec
 WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsLayout
 WriteSuccessExactTransactionsLiveSpec WriteSuccessExactTransactionsLiveFacts
 WriteSuccessExactTransactionsSourceAuthorizationLiveFrame
 WriteSuccessExactTransactionsSourceAuthorizationSpec
 WriteSuccessExactTransactionsSourceSuffixModel
 WriteSuccessExactTransactionsSourceSignatureContinuation
 WriteSuccessExactTransactionsSourceBackEdgeContinuation
 WriteSuccessExactTransactionsChainWordImage.

Lemma transactions_live_signature_guard `{!islaG Sigma} `{!threadG}
 sp base transactions processed transaction rest bytes tail (P : iProp Sigma) :
 transactionLoopSourceFacts sp base transactions processed (transaction :: rest) bytes ->
 writeSuccessCompleteNativeCode -∗
 □ instr_pre 0x14f04 (transactionLiveLoopState sp base transactions
   (processed ++ [transaction]) rest bytes tail P) -∗
 □ instr_pre 0x15620 (transactionSourceAuthorizationExit sp base bytes
   (length processed) (288 * length processed)
   (writeSuccessTransactionData transaction)
   (writeSuccessTransactionAccessBytes transaction)
   (transactionChainWordImage
     (transactionRowWord bytes (288 * length processed) 160)
     (transactionRowWord bytes (288 * length processed) 168))
   (writeSuccessTransactionAccessEntries transaction)
   (writeSuccessTransactionBlobBytes transaction)
   (writeSuccessTransactionAuthorizationBytes transaction)
   (transactionSourceSignatureEvents sp bytes (288 * length processed)
     (writeSuccessExactTransactionsEvents sp rest tail))
   (transactionLiveAuthorizationRemainder sp base transactions processed transaction rest bytes P)).
Proof.
 intros Hfacts. iStartProof. iIntros "#Hcode #Hnext".
 destruct Hfacts as
  (Hrelation & Hbytes & Hlength & Htotal & Halign & HstackLow & HstackHigh & Hbase).
 have HchainLength := proj2 (proj2 (transactions_chain_word_image
   (transactionRowWord bytes (288 * length processed) 160)
   (transactionRowWord bytes (288 * length processed) 168))).
 iPoseProof (transactions_source_back_edge_continuation sp base transactions processed
   transaction rest bytes
   (transactionChainWordImage
     (transactionRowWord bytes (288 * length processed) 160)
     (transactionRowWord bytes (288 * length processed) 168))
   tail P HchainLength with "Hcode Hnext") as "#Hback".
 iApply (transactions_source_signature_continuation sp base bytes (length processed)
   (288 * length processed) (writeSuccessTransactionData transaction)
   (writeSuccessTransactionAccessBytes transaction)
   (transactionChainWordImage
      (transactionRowWord bytes (288 * length processed) 160)
      (transactionRowWord bytes (288 * length processed) 168))
   (writeSuccessTransactionAccessEntries transaction)
   (writeSuccessTransactionBlobBytes transaction)
   (writeSuccessTransactionAuthorizationBytes transaction)
   (writeSuccessExactTransactionsEvents sp rest tail)
   (transactionLiveAuthorizationRemainder sp base transactions processed transaction rest bytes P)
   Halign HstackLow HstackHigh with "Hcode Hback").
Qed.
Print Assumptions transactions_live_signature_guard.
