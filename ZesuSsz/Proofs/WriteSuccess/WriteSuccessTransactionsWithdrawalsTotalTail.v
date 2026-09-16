Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost1568cWithdrawalsTotal.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPostWithdrawalsHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsTotalIntProvider.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsTotalTailCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsTotalTailLoads.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsTotalTailState.

Lemma write_success_transactions_withdrawals_total_int_provider_pre
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x1568c
    (writeSuccessTransactionsWithdrawalsTotalAt1568cSpec P) -∗
  □ instr_pre 0x15d10
    (writeSuccessTransactionsWithdrawalsTotalIntEntrySpec P).
Proof.
  iStartProof. iIntros "#Hint #Hreturn".
  iPoseProof "Hint" as "HintBody".
  iPoseProof "Hreturn" as "HreturnBody".
  iEval (rewrite instr_pre'_eq) in "HintBody".
  iEval (rewrite instr_pre'_eq) in "HreturnBody".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (write_success_transactions_withdrawals_total_int_provider P).
  - rewrite instr_pre'_eq. iExact "HintBody".
  - rewrite instr_pre'_eq. iExact "HreturnBody".
Qed.

Lemma write_success_transactions_withdrawals_total_tail
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15d10
    (writeSuccessTransactionsWithdrawalsTotalIntEntrySpec P) -∗
  instr_body 0x15678
    (writeSuccessTransactionsWithdrawalsTotalAt15678Spec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hint".
  iApply (write_success_transactions_withdrawals_total_tail_loads P with
    "Hlookup").
  iApply instr_pre_to_body. iNext.
  iApply (write_success_transactions_withdrawals_total_tail_call P with
    "Hlookup").
  iExact "Hint".
Qed.

Lemma write_success_transactions_withdrawals_total_to_branch
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x15694 (writeSuccessTransactionsPostWithdrawalsHandoff P) -∗
  instr_body 0x15678
    (writeSuccessTransactionsWithdrawalsTotalAt15678Spec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hint #Hloop".
  iAssert (□ instr_pre 0x1568c
    (writeSuccessTransactionsWithdrawalsTotalAt1568cSpec P))%I
    with "[]" as "#Hreturn".
  { iModIntro. iApply instr_pre_to_body. iNext.
    iApply (write_success_transactions_post_1568c_withdrawals_total P with
      "Hlookup Hloop"). }
  iPoseProof (write_success_transactions_withdrawals_total_int_provider_pre P
    with "Hint Hreturn") as "#Hprovider".
  iApply (write_success_transactions_withdrawals_total_tail P with
    "Hlookup Hprovider").
Qed.
