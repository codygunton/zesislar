Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary151b4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk1519cTo151a0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151a0To151ac.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151ac.

Lemma write_success_transactions_chunk_1519c
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15cb0 zesuEncoderU256CallSpec -∗
  instr_body 0x151b4 (writeSuccessTransactionsAt151b4Spec P) -∗
  instr_body 0x1519c (writeSuccessTransactionsAt1519cSpec P).
Proof.
  iIntros "#Hlookup #Hcode #Hu256 Hnext".
  iPoseProof (write_success_transactions_chunk_151ac P with
    "Hlookup Hcode Hu256 Hnext") as "H151ac".
  iPoseProof (write_success_transactions_chunk_151a0_to_151ac P with
    "Hlookup Hcode H151ac") as "H151a0".
  iApply (write_success_transactions_chunk_1519c_to_151a0 P with
    "Hlookup Hcode H151a0").
Qed.
