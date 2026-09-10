From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15668.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15668.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost1566c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15670.

Lemma write_success_transactions_post_15668_to_15674
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15674 (writeSuccessTransactionsPostAt15674Spec P) -∗
  instr_body 0x15668 (writeSuccessTransactionsPostAt15668Spec P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode Hnext".
  iApply (write_success_transactions_post_15668_load P with
    "Hlookup Hcode").
  iApply (write_success_transactions_post_1566c_load P with "Hlookup").
  iApply (write_success_transactions_post_15670_auipc P with "Hlookup").
  iExact "Hnext".
Qed.
