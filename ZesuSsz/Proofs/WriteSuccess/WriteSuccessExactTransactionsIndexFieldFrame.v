Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsIndexCell
  WriteSuccessExactTransactionsIndexSourceEntry WriteSuccessExactTransactionsLoopIndexEntry
  WriteSuccessExactTransactionsLiveFieldFrame WriteSuccessExactTransactionsSourceFieldLayout.

Lemma transactions_index_field_frame `{!islaG Sigma} `{!threadG}
    sp base transactions processed transaction rest bytes olddata tail (P : iProp Sigma) :
  transactionIndexCellEntry sp (Z_to_bv 64 base)
    (Z_to_bv 64 (Z.of_nat (length processed))) olddata
    (transactionIndexSourceCaller sp base bytes (length processed) tail
      (transactionLoopSourceFrame sp base transactions processed (transaction :: rest) bytes P)) ⊢
  transactionIndexCellEntry sp (Z_to_bv 64 base)
    (Z_to_bv 64 (Z.of_nat (length processed))) olddata
    (transactionIndexSourceCaller sp base bytes (length processed) tail
      ((bv_unsigned sp - 48) ↦ₘ? 48 ∗
       transactionFieldSourceHeap bytes (288 * length processed)
         (writeSuccessTransactionData transaction) (writeSuccessTransactionAccessBytes transaction)
         (writeSuccessTransactionAccessEntries transaction) ∗
       transactionLiveFieldFrame sp base transactions processed transaction rest bytes P ∗ True)%I).
Proof.
  have Hmapping : transactionLoopSourceFrame sp base transactions processed (transaction :: rest) bytes P ⊢
      (bv_unsigned sp - 48) ↦ₘ? 48 ∗
      transactionFieldSourceHeap bytes (288 * length processed)
        (writeSuccessTransactionData transaction) (writeSuccessTransactionAccessBytes transaction)
        (writeSuccessTransactionAccessEntries transaction) ∗
      transactionLiveFieldFrame sp base transactions processed transaction rest bytes P ∗ True.
  { iStartProof. iIntros "Hframe". iApply (transactions_live_field_frame with "Hframe"). }
  unfold transactionIndexCellEntry, transactionIndexSourceCaller, transactionIndexSourceData.
  repeat first [reflexivity | exact Hmapping | apply bi.sep_mono].
Qed.
Print Assumptions transactions_index_field_frame.
