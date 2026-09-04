From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150fc.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15100.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk150fcLoadSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk150fcLoadCore.

Lemma write_success_transactions_chunk_150fc_load
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15100 (writeSuccessTransactionsAt15100Spec P) -∗
  instr_body 0x150fc (writeSuccessTransactionsAt150fcSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt150fcSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail) "Hentry".
  iAssert (instr_body 0x15100
    (writeSuccessTransactions15100LoadPost P sp base transaction transactions
      processed remaining bytes prefix suffix tail))%I
    with "[Hnext]" as "HpostBody".
  { rewrite instr_pre'_eq. iIntros "Hpost".
    iApply "Hnext".
    rewrite /writeSuccessTransactionsAt15100Spec.
    iExists sp, base, transaction, transactions, processed, remaining,
      bytes, prefix, suffix, tail.
    iExact "Hpost". }
  iPoseProof (write_success_transactions_chunk_150fc_load_core P sp base
    transaction transactions processed remaining bytes prefix suffix tail with
    "Hlookup Hcode HpostBody") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody".
  iExact "Hentry".
Qed.
