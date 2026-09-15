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
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessNativeCode WriteSuccessExactTransactionsBackEdgeCompleteCode WriteSuccessExactTransactionsSourceSignatureBackEdgeEntry.
Lemma transactions_source_back_edge_continuation `{!islaG Sigma} `{!threadG}
 sp base transactions processed transaction rest bytes chainBytes tail (P : iProp Sigma) :
 length chainBytes = 16%nat ->
 writeSuccessCompleteNativeCode -∗
 □ instr_pre 0x14f04 (transactionLiveLoopState sp base transactions
  (processed ++ [transaction]) rest bytes tail P) -∗
 □ instr_pre 0x1565c (transactionSourceAuthorizationExit sp base bytes (length processed) (288 * length processed)
 (writeSuccessTransactionData transaction) (writeSuccessTransactionAccessBytes transaction) chainBytes
 (writeSuccessTransactionAccessEntries transaction) (writeSuccessTransactionBlobBytes transaction)
 (writeSuccessTransactionAuthorizationBytes transaction)
 (writeSuccessExactTransactionsEvents sp rest tail)
 (transactionLiveAuthorizationRemainder sp base transactions processed transaction rest bytes P)).
Proof.
 intros HchainLength. iIntros "#Hcode #Hnext".
 iAssert (□ instr_pre 0x14f04 (transactionBackEdgePost sp (Z_to_bv 64 (Z.of_nat (length processed))) (Z_to_bv 64 (Z.of_nat (length transactions))) (transactionLiveBackEdgeFrame sp base transactions processed transaction rest bytes tail P)))%I as "#Hpost".
 { iModIntro. iEval (rewrite instr_pre'_eq) in "Hnext".
   iEval (rewrite instr_pre'_eq). iNext. iIntros "Hreturned".
   iPoseProof (transactions_live_back_edge_handoff with "Hreturned") as "Hstate".
   iApply ("Hnext" with "Hstate"). }
 iModIntro. iEval (rewrite instr_pre'_eq). iNext. iIntros "Hsource".
 iPoseProof (transactions_source_signature_back_edge_entry sp base transactions processed transaction rest bytes chainBytes tail P
  HchainLength with "Hsource Hpost") as "Hentry".
 iPoseProof (transactions_back_edge_complete_code sp (Z_to_bv 64 (Z.of_nat (length processed))) (Z_to_bv 64 (Z.of_nat (length transactions))) (transactionLiveBackEdgeFrame sp base transactions processed transaction rest bytes tail P)
  with "Hcode") as "Hbody".
 iEval (rewrite instr_pre'_eq) in "Hbody".
 iApply ("Hbody" with "Hentry").
Qed.
Print Assumptions transactions_source_back_edge_continuation.
