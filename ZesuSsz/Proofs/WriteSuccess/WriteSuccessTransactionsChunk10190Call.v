From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150f0.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary10190.
Require Import ZesuSsz.Experiments.WriteSuccessTransactions10190Prepare.
Require Import ZesuSsz.Experiments.WriteSuccessTransactions10190Entry.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_10190_call
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_body 0x150f0 (writeSuccessTransactionsAt150f0Spec P) -∗
  instr_pre 0x10190 (writeSuccessTransactionsAt10190Spec P).
Proof.
  iIntros "#Houtput Hnext".
  iApply (instr_pre_wand 0x10190 0x10190 true true with "Houtput");
    [done | done |].
  rewrite /writeSuccessTransactionsAt10190Spec.
  iIntros "Hentry".
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining bytes prefix suffix tail)
    "Hentry".
  iPoseProof (write_success_transactions_10190_prepare P sp base transaction
    transactions processed remaining bytes prefix suffix tail with
    "Hnext Hentry") as "Hprepared".
  iApply (write_success_transactions_10190_prepared_to_call P sp base
    transaction transactions processed remaining bytes prefix suffix tail with
    "Hprepared").
Qed.
