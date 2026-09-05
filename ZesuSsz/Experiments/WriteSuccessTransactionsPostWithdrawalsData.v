Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost1568cWithdrawals.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsWithdrawalsTail.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsWithdrawalsTailState.

(** This continuation keeps the decoded withdrawals words at [1120(sp)] and
    [1128(sp)] through the byte-lists return point. *)
Lemma write_success_transactions_withdrawals_tail_to_post
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x1568c (writeSuccessTransactionsPost1568cWithdrawalsSpec P) -∗
  instr_body 0x15678 (writeSuccessTransactionsWithdrawalsAt15678Spec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hint #Hwithdrawals".
  iPoseProof (write_success_transactions_withdrawals_int_provider_pre P with
    "Hint Hwithdrawals") as "#Hprovider".
  iApply (write_success_transactions_withdrawals_tail P with
    "Hlookup Hprovider").
Qed.

Lemma write_success_transactions_withdrawals_tail_to_post_pre
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x1568c (writeSuccessTransactionsPost1568cWithdrawalsSpec P) -∗
  □ instr_pre 0x15678 (writeSuccessTransactionsWithdrawalsAt15678Spec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hint #Hwithdrawals". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply (write_success_transactions_withdrawals_tail_to_post P with
    "Hlookup Hint Hwithdrawals").
Qed.
