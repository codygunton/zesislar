Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150f0Spec.

Lemma write_success_transactions_invariant_bound
    `{!islaG Sigma}
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) :
  WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant
      sp base transactions processed (transaction :: remaining)
      bytes prefix suffix -∗
  WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant
      sp base transactions processed (transaction :: remaining)
      bytes prefix suffix ∗
  ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
  ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
  ⌜0x20000000 <= bv_unsigned sp - 48⌝.
Proof.
  iIntros "#Hinv".
  iPoseProof "Hinv" as "#Hcopy".
  iEval (rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant)
    in "Hcopy".
  iDestruct "Hcopy" as
    "(%H0 & %H1 & %H2 & %H3 & %H4 & %H5 & %H6 & %H7 & %H8 &
      %H9 & %H10 & %H11 & %H12 & %H13 & %H14 & _)".
  iSplit.
  - iExact "Hinv".
  - iSplit.
    + iPureIntro. exact H11.
    + iSplit.
      * iPureIntro. exact H9.
      * iPureIntro. exact H10.
Qed.
