From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15668WithdrawalsTotalStates.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15668WithdrawalsTotal.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost1566cWithdrawalsTotal.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15670WithdrawalsTotal.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15674WithdrawalsTotal.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15678WithdrawalsTotalAdapter.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPostWithdrawalsHandoff.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsWithdrawalsTotalResources.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsSpec.

Definition writeSuccessTransactionsCarrierWithdrawalsTotalExitSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (transactionBase withdrawalBase : Z)
    (transactions : list writeSuccessTransaction) (transactionBytes : list (bv 8))
    (count : nat) (withdrawalBytes : list (bv 8)) (tail : spec)
    (first second : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (writeSuccessTransactionsLoopCarrierExit
     (writeSuccessTransactionsCarrierWithdrawalsTotalData P sp pointer
       transactionBase withdrawalBase transactions transactionBytes count
       withdrawalBytes tail first second items)
     sp transactionBase transactions transactionBytes
     (writeSuccessWithdrawalsEvents sp count tail) first second pointer
     (Z_to_bv 64 (Z.of_nat count)) items ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsCarrierWithdrawalsTotalExitSpec) := I.

Lemma write_success_transactions_carrier_withdrawals_total_exit_adapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (transactionBase withdrawalBase : Z)
    (transactions : list writeSuccessTransaction) (transactionBytes : list (bv 8))
    (count : nat) (withdrawalBytes : list (bv 8)) (tail : spec)
    (first second : bv 64) (items : list ByteListItem) :
  writeSuccessTransactionsCarrierWithdrawalsTotalExitSpec P sp pointer
    transactionBase withdrawalBase transactions transactionBytes count
    withdrawalBytes tail first second items -∗
  writeSuccessTransactionsPost15668WithdrawalsTotalSpec P sp pointer
    transactionBase withdrawalBase transactions transactionBytes count
    withdrawalBytes tail first second items.
Proof.
  iStartProof. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsCarrierWithdrawalsTotalExitSpec)
    in "Hentry".
  iDestruct "Hentry" as
    "(Hexit & %Halign16 & %Halign8 & %Hlow & %Hhigh & _)".
  iEval (rewrite /writeSuccessTransactionsLoopCarrierExit) in "Hexit".
  iDestruct "Hexit" as
    "(Hsys & Hother & H2 & H10 & H11 & HtransactionBytes & Hown & Hscratch &
      Hcarrier & HupperScratch & Hmmio & Htrace & Hdata & _)".
  iEval (rewrite /writeSuccessTransactionsPost15668WithdrawalsTotalSpec
    /writeSuccessTransactionsPost15668WithdrawalsTotalFrame).
  iFrame "Hsys Hother H2 H10 H11 HtransactionBytes Hown Hscratch Hcarrier
    HupperScratch Hmmio Htrace Hdata".
  repeat iSplit; try iPureIntro; try assumption; try done.
Qed.

Lemma write_success_transactions_carrier_withdrawals_total_provider
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
  instr_body 0x15668
    (writeSuccessTransactionsCarrierWithdrawalsTotalExitSpec P sp pointer
      transactionBase withdrawalBase transactions transactionBytes count
      withdrawalBytes tail first second items).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #HbyteLists #Hint #Hloop".
  iPoseProof (write_success_transactions_post_15668_withdrawals_total P sp pointer
      transactionBase withdrawalBase transactions transactionBytes count
      withdrawalBytes tail first second items with "Hlookup") as "Hchain".
  iSpecialize ("Hchain" with "[-]").
  { iApply (write_success_transactions_post_1566c_withdrawals_total P sp pointer
      transactionBase withdrawalBase transactions transactionBytes count
      withdrawalBytes tail first second items with "Hlookup").
    iApply (write_success_transactions_post_15670_withdrawals_total P sp pointer
      transactionBase withdrawalBase transactions transactionBytes count
      withdrawalBytes tail first second items with "Hlookup").
    iApply (write_success_transactions_post_15674_withdrawals_total P sp pointer
      transactionBase withdrawalBase transactions transactionBytes count
      withdrawalBytes tail first second items with
      "Hlookup Hcode HbyteLists Hint Hloop"). }
  rewrite instr_pre'_eq. iIntros "Hentry".
  iApply "Hchain".
  iApply (write_success_transactions_carrier_withdrawals_total_exit_adapter P
    sp pointer transactionBase withdrawalBase transactions transactionBytes
    count withdrawalBytes tail first second items with "Hentry").
Qed.
