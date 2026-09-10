From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierWithdrawalsTotalProvider.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopCarrierAt14f00.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopCarrierEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopCarrierProvider.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPostWithdrawalsHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsTotalResources.

Lemma write_success_transactions_loop_carrier_14f04_pre
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  □ instr_body 0x14f08 (writeSuccessTransactionsAt14f08CarrierSpec P) -∗
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x14f04 (writeSuccessTransactionsLoopCarrierSpec P).
Proof.
  iStartProof. iIntros "#Hbody #Hlookup".
  iLöb as "IH".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (write_success_transactions_loop_carrier_provider P with
    "Hbody Hlookup IH").
Qed.

Lemma write_success_transactions_loop_carrier_14f00_pre
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  □ instr_body 0x14f08 (writeSuccessTransactionsAt14f08CarrierSpec P) -∗
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x14f00 (writeSuccessTransactionsLoopCarrierAt14f00Spec P).
Proof.
  iStartProof. iIntros "#Hbody #Hlookup".
  iPoseProof (write_success_transactions_loop_carrier_14f04_pre P with
    "Hbody Hlookup") as "#Hloop".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (write_success_transactions_loop_carrier_14f00_load P with
    "Hlookup").
  iApply "Hloop".
Qed.

Lemma write_success_transactions_carrier_withdrawals_total_provider_pre
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (transactionBase withdrawalBase : Z)
    (transactions : list writeSuccessTransaction) (transactionBytes : list (bv 8))
    (count : nat) (withdrawalBytes : list (bv 8)) (tail : spec)
    (first second : bv 64) (items : list ByteListItem) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c10 zesuEncoderByteListsCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x15694
    (writeSuccessTransactionsPostWithdrawalsHandoff
      (writeSuccessTransactionsPost15678PreservedScratch sp transactionBase
         (length transactions) first second items ∗
       transactionBase ↦ₘ∗ transactionBytes ∗
       writeSuccessTransactionsOwn transactions ∗ P)) -∗
  □ instr_pre 0x15668
    (writeSuccessTransactionsCarrierWithdrawalsTotalExitSpec P sp pointer
      transactionBase withdrawalBase transactions transactionBytes count
      withdrawalBytes tail first second items).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #HbyteLists #Hint #Hloop".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (write_success_transactions_carrier_withdrawals_total_provider P sp
    pointer transactionBase withdrawalBase transactions transactionBytes count
    withdrawalBytes tail first second items with
    "Hlookup Hcode HbyteLists Hint Hloop").
Qed.
