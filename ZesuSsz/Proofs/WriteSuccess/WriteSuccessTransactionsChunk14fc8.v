Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14fc8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15028.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14fc8To14fe0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14fe0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14fe4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14fe8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14fec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk14ff0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15018.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk1501c.

Lemma write_success_transactions_chunk_14fc8
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15028 (writeSuccessTransactionsAt15028Spec P) -∗
  instr_body 0x14fc8 (writeSuccessTransactionsAt14fc8Spec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iPoseProof (write_success_transactions_chunk_1501c P with
    "Hlookup Hcode Hnext") as "H1501c".
  iPoseProof (write_success_transactions_chunk_15018 P with
    "Hlookup Hcode H1501c") as "H15018".
  iPoseProof (write_success_transactions_chunk_14ff0 P with
    "Hlookup Hcode H15018") as "H14ff0".
  iPoseProof (write_success_transactions_chunk_14fec P with
    "Hlookup Hcode H14ff0") as "H14fec".
  iPoseProof (write_success_transactions_chunk_14fe8 P with
    "Hlookup Hcode H14fec") as "H14fe8".
  iPoseProof (write_success_transactions_chunk_14fe4 P with
    "Hlookup Hcode H14fe8") as "H14fe4".
  iPoseProof (write_success_transactions_chunk_14fe0 P with
    "Hlookup Hcode H14fe4") as "H14fe0".
  iApply (write_success_transactions_chunk_14fc8_to_14fe0 P with
    "Hlookup Hcode H14fe0").
Qed.
