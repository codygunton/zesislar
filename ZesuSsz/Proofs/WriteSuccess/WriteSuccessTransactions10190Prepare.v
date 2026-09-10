From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150ecCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150f0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150ecJump.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactions10190MachineAdapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactions10190Return.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary10190Prepared.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactions10190ReturnBuilder.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactions10190Framed.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactions10190FrameFacts.

Lemma write_success_transactions_10190_prepare
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_body 0x150f0 (writeSuccessTransactionsAt150f0Spec P) -∗
  writeSuccessTransactionsAt10190Block P sp base transaction transactions
    processed remaining bytes prefix suffix tail -∗
  writeSuccessTransactionsAt10190PreparedBlock P sp base transaction
    transactions processed remaining bytes prefix suffix tail.
Proof.
  iIntros "Hnext Hentry".
  iPoseProof (write_success_transactions_10190_frame P sp base transaction
    transactions processed remaining bytes prefix suffix tail with "Hentry")
    as "Hframed".
  iPoseProof (write_success_transactions_10190_framed_unpack P sp base
    transaction transactions processed remaining bytes prefix suffix tail with
    "Hframed") as "(HmachineFrame & Hmmio & Htrace & Hframe & _)".
  iPoseProof (write_success_transactions_10190_frame_facts P sp base transaction
    transactions processed remaining bytes prefix suffix tail with "Hframe") as
    "(Hframe & %HspAlign & %HspMin & %HspMax)".
  iPoseProof (write_success_transactions_10190_return_builder P sp base
    transaction transactions processed remaining bytes prefix suffix tail with
    "Hnext Hframe") as "Hreturn".
  iApply (write_success_transactions_10190_prepared_pack P sp base transaction
    transactions processed remaining bytes prefix suffix tail with
    "HmachineFrame [] [] [] Hmmio Htrace Hreturn").
  - iPureIntro. exact HspAlign.
  - iPureIntro. exact HspMin.
  - iPureIntro. exact HspMax.
Qed.
