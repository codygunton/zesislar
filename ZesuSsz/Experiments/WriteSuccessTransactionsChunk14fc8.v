Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14fc8.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15028.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk14fc8Prefix.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk1501c.

Lemma write_success_transactions_chunk_14fc8
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15028 (writeSuccessTransactionsAt15028Spec P) -∗
  instr_body 0x14fc8 (writeSuccessTransactionsAt14fc8Spec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iPoseProof (write_success_transactions_chunk_1501c P with
    "Hlookup Hcode Hnext") as "Hsuffix".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt14fc8Spec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hmachine & Harray & Hframe & Hfacts & _)".
  iEval (rewrite -instr_pre'_eq) in "Hsuffix".
  iPoseProof (write_success_transactions_chunk_14fc8_prefix P sp base
    transaction transactions processed remaining bytes prefix suffix tail with
    "Hlookup Hcode Hsuffix") as "Hprefix".
  iEval (rewrite instr_pre'_eq) in "Hprefix".
  iApply "Hprefix".
  rewrite /writeSuccessTransactionsAt14fc8Prefix.
  iFrame.
Qed.
