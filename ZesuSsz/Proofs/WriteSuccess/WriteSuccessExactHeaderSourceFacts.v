Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsLiveSpec.
Lemma write_success_exact_header_source_facts `{!islaG Sigma}
    sp base transactions processed remaining bytes prefix suffix :
  writeSuccessTransactionsInvariant sp base transactions processed remaining bytes prefix suffix -∗
  ⌜transactionLoopSourceFacts sp base transactions processed remaining bytes⌝.
Proof.
  rewrite /writeSuccessTransactionsInvariant.
  iIntros "(%Hparts & %Hbytes & _ & _ & _ & %Hlength & _ & _ & %Hcount & %Halign & %Hmin & %Hmax & %Hbasealign & %Hbasemin & %Hbasemax & _)".
  iPureIntro. unfold transactionLoopSourceFacts.
  repeat split; assumption.
Qed.
Print Assumptions write_success_exact_header_source_facts.
