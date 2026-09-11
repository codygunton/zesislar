Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost1568cWithdrawals.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsProvider.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsTailCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsTailLoads.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsTailState.

Lemma write_success_transactions_withdrawals_int_provider_pre
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x1568c (writeSuccessTransactionsPost1568cWithdrawalsSpec P) -∗
  □ instr_pre 0x15d10
    (writeSuccessTransactionsWithdrawalsIntEntrySpec P).
Proof.
  iStartProof. iIntros "#Hint #Hwithdrawals".
  iPoseProof "Hint" as "HintBody".
  iPoseProof "Hwithdrawals" as "HwithdrawalsBody".
  iEval (rewrite instr_pre'_eq) in "HintBody".
  iEval (rewrite instr_pre'_eq) in "HwithdrawalsBody".
  iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply (write_success_transactions_withdrawals_int_provider P).
  - rewrite instr_pre'_eq. iExact "HintBody".
  - rewrite instr_pre'_eq. iExact "HwithdrawalsBody".
Qed.

Lemma write_success_transactions_withdrawals_tail
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15d10
    (writeSuccessTransactionsWithdrawalsIntEntrySpec P) -∗
  instr_body 0x15678 (writeSuccessTransactionsWithdrawalsAt15678Spec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hint".
  iApply (write_success_transactions_withdrawals_tail_loads P with "Hlookup").
  iApply instr_pre_to_body. iNext.
  iApply (write_success_transactions_withdrawals_tail_call P with "Hlookup").
  iExact "Hint".
Qed.

Lemma write_success_transactions_withdrawals_tail_pre
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15d10
    (writeSuccessTransactionsWithdrawalsIntEntrySpec P) -∗
  □ instr_pre 0x15678 (writeSuccessTransactionsWithdrawalsAt15678Spec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hint". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply (write_success_transactions_withdrawals_tail P with "Hlookup Hint").
Qed.
