Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674DataCallJalrStrong.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15678WithdrawalsTotalAdapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPostWithdrawalsHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsTotalTail.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsTotalResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessWithdrawalsSpec.

Lemma write_success_transactions_post_15678_withdrawals_total
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp first second pointer : bv 64)
    (transactionBase withdrawalBase : Z) (transactionTotal count : nat)
    (items : list ByteListItem) (bytes : list (bv 8)) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x15694
    (writeSuccessTransactionsPostWithdrawalsHandoff
      (writeSuccessTransactionsPost15678PreservedScratch sp transactionBase
        transactionTotal first second items ∗ P)) -∗
  instr_body 0x15678
    (writeSuccessTransactionsPost15674DataCallReturnFixedSpec
      (writeSuccessTransactionsPost15678WithdrawalsTotalData P sp pointer
        withdrawalBase count bytes tail
        (writeSuccessTransactionsPost15678PreservedScratch sp transactionBase
          transactionTotal first second items))
      sp transactionBase transactionTotal
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessWithdrawalsEvents sp count tail))
      first second pointer (Z_to_bv 64 (Z.of_nat count)) items).
Proof.
  iStartProof. iIntros "#Hlookup #Hint #Hloop".
  iPoseProof (write_success_transactions_withdrawals_total_to_branch
    (writeSuccessTransactionsPost15678PreservedScratch sp transactionBase
      transactionTotal first second items ∗ P) with "Hlookup Hint Hloop")
    as "Htail".
  iApply (instr_pre_wand 0x15678 0x15678 false false with "Htail");
    [done | done |].
  iIntros "Hreturn".
  iApply (write_success_transactions_post_15678_withdrawals_total_adapter P
    sp first second pointer transactionBase withdrawalBase transactionTotal
    count items bytes tail with "Hreturn").
Qed.
