From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15028.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15048.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk15028Prefix.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk15044Load.

Lemma write_success_transactions_chunk_15028
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15048 (writeSuccessTransactionsAt15048Spec P) -∗
  instr_body 0x15028 (writeSuccessTransactionsAt15028Spec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iPoseProof "Hlookup" as "#Hlookup15044".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15044".
  iPoseProof ("Hlookup15044" $! 0x15044) as "Hinstr".
  iSpecialize ("Hinstr" with "[]").
  { iPureIntro. rewrite Index.lookup_a15044. done. }
  iEval (rewrite Index.lookup_a15044) in "Hinstr".
  iPoseProof (write_success_transactions_chunk_15044_load P with
    "Hinstr Hnext") as "Hsuffix".
  iApply (write_success_transactions_chunk_15028_prefix P with
    "Hlookup Hcode Hsuffix").
Qed.
