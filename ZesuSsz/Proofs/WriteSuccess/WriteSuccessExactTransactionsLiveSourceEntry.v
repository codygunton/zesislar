Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.NatBounds.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessTransactionsSpec WriteSuccessExactTransactionsSpec
  WriteSuccessExactTransactionsLiveSpec WriteSuccessExactTransactionsLiveFacts
  WriteSuccessExactTransactionsLiveSourceRegion WriteSuccessExactTransactionsLoopIndexEntry
  WriteSuccessExactTransactionsLiveFieldFrame WriteSuccessExactTransactionsSourceFieldEvents
  WriteSuccessExactTransactionsChainWordImage WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactTransactionsBlobCountTailModel.

Lemma transactions_live_source_entry_correct `{!islaG Sigma} `{!threadG}
    sp base transactions processed transaction rest bytes tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x153d0 (transactionSourceFieldPost sp base bytes (length processed)
    (288 * length processed) (writeSuccessTransactionData transaction)
    (writeSuccessTransactionAccessBytes transaction)
    (transactionChainWordImage (transactionRowWord bytes (288 * length processed) 160)
      (transactionRowWord bytes (288 * length processed) 168))
    (writeSuccessTransactionAccessEntries transaction)
    (writeSuccessExactTransactionAfterBlobCountEvents sp transaction
      (writeSuccessExactTransactionsEvents sp rest tail))
    (transactionLiveFieldFrame sp base transactions processed transaction rest bytes P)) -∗
  instr_body 0x14f08
    (transactionLiveLoopState sp base transactions processed (transaction :: rest) bytes tail P).
Proof.
  iStartProof. iIntros "#Hcode #Hnext".
  iEval (rewrite instr_pre'_eq). iIntros "Hstate".
  iDestruct (transactions_live_state_facts with "Hstate") as "(Hstate & %Hvalid & %Hfacts & _)".
  have Hrelation := proj1 Hfacts.
  rewrite Hrelation in Hvalid. apply Forall_app in Hvalid as [Hprefix Hremaining].
  have Htransaction := Forall_inv Hremaining.
  iPoseProof (transactions_live_source_region_correct sp base transactions processed transaction rest
    bytes tail P Hfacts Hprefix Htransaction with "Hcode Hnext") as "Hregion".
  iEval (rewrite instr_pre'_eq) in "Hregion".
  iApply "Hregion". iApply (transactions_loop_to_index with "Hstate").
Qed.
Print Assumptions transactions_live_source_entry_correct.
