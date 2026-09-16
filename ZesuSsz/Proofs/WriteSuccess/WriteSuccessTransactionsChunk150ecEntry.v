Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150ec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150ecCall.

Lemma write_success_transactions_chunk_150ec_entry
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_body 0x150ec (writeSuccessTransactionsAt150ecCallSpec P) -∗
  instr_body 0x150ec (writeSuccessTransactionsAt150ecSpec P).
Proof.
  rewrite !instr_pre'_eq.
  iIntros "Hnext Hentry".
  rewrite /writeSuccessTransactionsAt150ecSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hsys & H1 & Hcontext)".
  iEval (unfold writeSuccessTransactionsContext150e8) in "Hcontext".
  iDestruct "Hcontext" as
    "(Hmachine & Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining &
      Hmmio & Htrace & HP & Hinv & Hexit & _)".
  iApply "Hnext".
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iFrame "Hsys H1 Hmachine Hmmio Htrace".
  rewrite /writeSuccessTransactions150ecCallFrame.
  iFrame.
Qed.
