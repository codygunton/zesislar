From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150ecCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150ecJump.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary10190Prepared.

Definition writeSuccessTransactionsAt10190FramedBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (writeSuccessTransactions10190OpaqueMachineFrame
      sp base transaction transactions processed ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace
     (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 1)
       (writeSuccessTransactionPhaseEvents TransactionChainId sp transaction
         (writeSuccessTransactionsEvents sp remaining tail))) ∗
   writeSuccessTransactions150ecCallFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗ True)%I.

Lemma write_success_transactions_10190_frame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  writeSuccessTransactionsAt10190Block P sp base transaction transactions
    processed remaining bytes prefix suffix tail -∗
  writeSuccessTransactionsAt10190FramedBlock P sp base transaction transactions
    processed remaining bytes prefix suffix tail.
Proof.
  iIntros "Hblock".
  iPoseProof (write_success_transactions_at10190_block_unpack P sp base
    transaction transactions processed remaining bytes prefix suffix tail with
    "Hblock") as
    "(Hsys & H1 & Hmachine & Hmmio & Htrace & Hframe & _)".
  iPoseProof (write_success_transactions_10190_machine_frame_pack sp base
    transaction transactions processed with "Hsys H1 Hmachine")
    as "HmachineFrame".
  rewrite /writeSuccessTransactionsAt10190FramedBlock.
  iFrame "HmachineFrame Hmmio Htrace Hframe".
Qed.

Lemma write_success_transactions_10190_framed_unpack
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  writeSuccessTransactionsAt10190FramedBlock P sp base transaction transactions
    processed remaining bytes prefix suffix tail -∗
  writeSuccessTransactions10190OpaqueMachineFrame
      sp base transaction transactions processed ∗
  mmio_range 0x2401a0c0 16 ∗
  spec_trace
    (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 1)
      (writeSuccessTransactionPhaseEvents TransactionChainId sp transaction
        (writeSuccessTransactionsEvents sp remaining tail))) ∗
  writeSuccessTransactions150ecCallFrame P sp base transaction
    transactions processed remaining bytes prefix suffix tail ∗ True.
Proof.
  rewrite /writeSuccessTransactionsAt10190FramedBlock.
  iIntros "Hframe". iExact "Hframe".
Qed.

Global Opaque writeSuccessTransactionsAt10190FramedBlock.
