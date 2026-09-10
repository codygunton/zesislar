Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15668Data.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost1566cData.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15670Data.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674Data.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPostWithdrawalsData.

Lemma write_success_transactions_post_15668_data_chain
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c10 zesuEncoderByteListsCallSpec -∗
  instr_body 0x15678 (writeSuccessTransactionsPost15678DataSpec P) -∗
  instr_body 0x15668 (writeSuccessTransactionsPostAt15668DataSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Hcallee Hnext".
  iApply (write_success_transactions_post_15668_data P with "Hlookup").
  iApply (write_success_transactions_post_1566c_data P with "Hlookup").
  iApply (write_success_transactions_post_15670_data P with "Hlookup").
  iApply (write_success_transactions_post_15674_data P with
    "Hlookup Hcode Hcallee Hnext").
Qed.
