Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151a0To151a4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151a4To151ac.

Lemma write_success_transactions_chunk_151a0_to_151ac
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x151ac (writeSuccessTransactionsAt151acSpec P) -∗
  instr_body 0x151a0 (writeSuccessTransactionsAt151a0Spec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iPoseProof (write_success_transactions_chunk_151a4_to_151ac P with
    "Hlookup Hcode Hnext") as "H151a4".
  iApply (write_success_transactions_chunk_151a0_to_151a4 P with
    "Hlookup Hcode H151a4").
Qed.
