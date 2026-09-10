From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Lemma write_success_transactions_chunk_15088_load_array_prepare
    `{!islaG Sigma} `{!threadG} (base : Z) (processed : nat)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
  ⌜length
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction) =
    288%nat⌝ -∗
  (base + 288 * Z.of_nat processed) ↦ₘ∗
    WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction -∗
  (base + 288 * Z.of_nat processed) ↦ₘ∗
    take 120
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction) ∗
  (base + 288 * Z.of_nat processed + 120) ↦ₘ
    WriteSuccessTransactionsSpec.writeSuccessTransactionWord
      transaction 120 ∗
  (base + 288 * Z.of_nat processed + 128) ↦ₘ∗
    drop 128
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction).
Proof.
  iIntros (Hlength) "Harray".
  iEval (rewrite <-(take_drop 120
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)))
    in "Harray".
  iDestruct (mem_mapsto_array_app with "Harray") as
    "(Hprefix & Hrest)".
  have HprefixLength :
    length
      (take 120
        (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
          transaction)) = 120%nat by rewrite length_take Hlength; lia.
  iEval (rewrite HprefixLength; cbn) in "Hrest".
  iEval (rewrite <-(take_drop 8
    (drop 120
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction)))) in "Hrest".
  iDestruct (mem_mapsto_array_app with "Hrest") as
    "(HwordBytes & Hsuffix)".
  have HwordLength :
    length
      (take 8
        (drop 120
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction))) = 8%nat.
  { rewrite length_take length_drop Hlength. lia. }
  iPoseProof (mem_mapsto_byte_array_to_mapsto with "HwordBytes") as "Hword".
  iEval (rewrite HwordLength; cbn) in "Hword".
  iEval (rewrite HwordLength; cbn; rewrite drop_drop) in "Hsuffix".
  have HsuffixAddress :
    (base + 288 * Z.of_nat processed + Z.of_N (8 `div` 8) * 120%nat +
      Z.of_N (8 `div` 8) * 8%nat =
     base + 288 * Z.of_nat processed + 128)%Z by cbn; lia.
  iEval (rewrite HsuffixAddress) in "Hsuffix".
  iFrame "Hprefix Hword Hsuffix".
Qed.
