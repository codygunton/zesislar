Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Lemma write_success_transactions_valid_frame
    `{!islaG Sigma} (transaction : writeSuccessTransaction) :
  writeSuccessTransactionOwn transaction -∗
  ⌜writeSuccessTransactionValid transaction⌝ ∗
  writeSuccessTransactionOwn transaction.
Proof.
  rewrite /writeSuccessTransactionOwn.
  iIntros "(Hdata & Haccess & Hentries & Hblob & Hauthorization &
    %Hvalid & _)".
  iFrame. iPureIntro. naive_solver.
Qed.
