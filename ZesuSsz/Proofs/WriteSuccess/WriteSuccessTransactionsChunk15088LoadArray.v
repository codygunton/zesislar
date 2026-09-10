From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Lemma write_success_transactions_chunk_15088_load_array
    `{!islaG Sigma} `{!threadG} (base : Z) (processed : nat)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
  (base + 288 * Z.of_nat processed) ↦ₘ∗
    take 120
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction) -∗
  (base + 288 * Z.of_nat processed + 128) ↦ₘ∗
    drop 128
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction) -∗
  (base + 288 * Z.of_nat processed + 120) ↦ₘ
    WriteSuccessTransactionsSpec.writeSuccessTransactionWord
      transaction 120 -∗
  ⌜length
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction) =
    288%nat⌝ -∗
  (base + 288 * Z.of_nat processed) ↦ₘ∗
    WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction.
Proof.
  iIntros "Hprefix Hsuffix Hword" (Hlength).
  iApply (mem_mapsto_array_recombine_u64_read
    (base + 288 * Z.of_nat processed)
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    120 _ _ with "Hprefix Hsuffix Hword [] [] []").
  - iPureIntro. cbn. lia.
  - iPureIntro. cbn. lia.
  - iPureIntro. rewrite Hlength. lia.
Qed.
