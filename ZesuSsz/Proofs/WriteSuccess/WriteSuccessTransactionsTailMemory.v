Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsTailHelpers.

Import ListNotations.

Lemma write_success_transactions_memory_snoc
    `{!islaG Sigma} `{!threadG}
    (base : Z) (transaction : writeSuccessTransaction)
    (processed remaining : list writeSuccessTransaction)
    (prefix suffix : list (bv 8)) :
  ⌜prefix = writeSuccessTransactionsBytes processed⌝ -∗
  ⌜suffix =
    writeSuccessTransactionBytes transaction ++
    writeSuccessTransactionsBytes remaining⌝ -∗
  ⌜length prefix = (288 * length processed)%nat⌝ -∗
  ⌜length (writeSuccessTransactionBytes transaction) = 288%nat⌝ -∗
  base ↦ₘ∗ prefix -∗
  (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix -∗
  base ↦ₘ∗ writeSuccessTransactionsBytes (processed ++ [transaction]) ∗
  (base + 288 * Z.of_nat (length (processed ++ [transaction]))) ↦ₘ∗
    writeSuccessTransactionsBytes remaining.
Proof.
  iIntros (HprefixEq HsuffixEq HprefixLength HtransactionLength)
    "HbasePrefix HbaseSuffix".
  iEval (rewrite HsuffixEq) in "HbaseSuffix".
  iDestruct (IslarisMemory.mem_mapsto_array_app 8%N
    (base + 288 * Z.of_nat (length processed)) (DfracOwn 1)
    (writeSuccessTransactionBytes transaction)
    (writeSuccessTransactionsBytes remaining) with "HbaseSuffix") as
    "[HtransactionBytes HremainingBytes]".
  have HtransactionAddress :
      (base + 288 * Z.of_nat (length processed))%Z =
      (base + Z.of_N (8 `div` 8) *
        Z.of_nat ((288 * length processed)%nat))%Z by
    (replace (Z.of_N (8 `div` 8)) with 1%Z by reflexivity;
     rewrite Nat2Z.inj_mul; cbn; lia).
  iEval (rewrite HtransactionAddress) in "HtransactionBytes".
  iPoseProof (IslarisMemory.mem_mapsto_array_app_combine_at 8%N base
    (DfracOwn 1) prefix (writeSuccessTransactionBytes transaction)
    (288 * length processed)%nat HprefixLength with
    "HbasePrefix HtransactionBytes") as "HbasePrefixNew".
  have HprefixNewEq :
      prefix ++ writeSuccessTransactionBytes transaction =
      writeSuccessTransactionsBytes (processed ++ [transaction]) by
    (rewrite write_success_transactions_bytes_app /= app_nil_r -HprefixEq;
     reflexivity).
  iEval (rewrite HprefixNewEq) in "HbasePrefixNew".
  have HremainingAddress :
      (base + 288 * Z.of_nat (length processed) +
        Z.of_N (8 `div` 8) *
          Z.of_nat (length (writeSuccessTransactionBytes transaction)))%Z =
      (base + 288 * Z.of_nat (length (processed ++ [transaction])))%Z by
    (replace (Z.of_N (8 `div` 8)) with 1%Z by reflexivity;
     rewrite HtransactionLength length_app Nat2Z.inj_add; cbn; lia).
  iEval (rewrite HremainingAddress) in "HremainingBytes".
  iFrame.
Qed.
