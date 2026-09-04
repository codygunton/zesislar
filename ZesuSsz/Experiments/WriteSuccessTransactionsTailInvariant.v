From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsTailHelpers.

Import ListNotations.

Lemma write_success_transactions_invariant_snoc
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z)
    (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) :
  ⌜length (writeSuccessTransactionBytes transaction) = 288%nat⌝ -∗
  writeSuccessTransactionsInvariant sp base transactions processed
    (transaction :: remaining) bytes prefix suffix -∗
  writeSuccessTransactionsInvariant sp base transactions
    (processed ++ [transaction]) remaining bytes
    (writeSuccessTransactionsBytes (processed ++ [transaction]))
    (writeSuccessTransactionsBytes remaining).
Proof.
  iIntros (HtransactionLength) "Hinv".
  iDestruct "Hinv" as
    "(%HtransactionsEq & HbytesEqI & %HprefixEq & %HsuffixEq &
      _ & HbytesLengthI & %HprefixLength & HsuffixLengthI & HtransactionsBoundI &
      HspAlignI & HspLowI & HspHighI & HbaseAlignI & HbaseLowI &
      HbaseHighI & _)".
  iPoseProof "HbytesEqI" as "#HbytesEqCopy".
  iDestruct "HbytesEqCopy" as %HbytesEq.
  iPoseProof "HbytesLengthI" as "#HbytesLengthCopy".
  iDestruct "HbytesLengthCopy" as %HbytesLength.
  iPoseProof "HsuffixLengthI" as "#HsuffixLengthCopy".
  iDestruct "HsuffixLengthCopy" as %HsuffixLength.
  have HtransactionsNew :
      transactions = (processed ++ [transaction]) ++ remaining by
    (rewrite HtransactionsEq -app_assoc; reflexivity).
  have HbytesSplitNew :
      bytes =
        writeSuccessTransactionsBytes (processed ++ [transaction]) ++
        writeSuccessTransactionsBytes remaining by
    (rewrite HbytesEq HtransactionsNew write_success_transactions_bytes_app;
     reflexivity).
  have HprocessedLength :
      length (writeSuccessTransactionsBytes processed) =
      (288 * length processed)%nat by
    (rewrite -HprefixEq; exact HprefixLength).
  have HprefixLengthNew :
      length (writeSuccessTransactionsBytes (processed ++ [transaction])) =
      (288 * length (processed ++ [transaction]))%nat by
    (rewrite write_success_transactions_bytes_app; cbn;
     rewrite !app_nil_r !length_app HprocessedLength HtransactionLength;
     cbn; lia).
  have HsuffixLengthNew :
      length (writeSuccessTransactionsBytes remaining) =
      (288 * length remaining)%nat by
    (rewrite HsuffixEq /= length_app HtransactionLength in HsuffixLength;
     cbn in HsuffixLength; nia).
  rewrite /writeSuccessTransactionsInvariant.
  iFrame "HtransactionsBoundI HspAlignI HspLowI HspHighI HbaseAlignI
    HbaseLowI HbaseHighI".
  repeat iSplit; try iPureIntro; try done.
Qed.
