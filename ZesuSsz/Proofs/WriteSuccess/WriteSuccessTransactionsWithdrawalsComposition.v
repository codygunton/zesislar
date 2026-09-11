Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopEventsPost.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15668Events.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674Events.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost1567c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15680.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15684.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15688.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost1568cWithdrawals.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPostWithdrawalsData.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsPayload.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsTailState.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessWithdrawalsLoop.

(** This contract isolates the missing relation between the two words loaded
    from the outer frame and the structured withdrawals resources. *)
Definition writeSuccessTransactionsWithdrawalsAdapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (instr_body 0x1568c (writeSuccessTransactionsPost1568cWithdrawalsSpec P) -∗
   instr_body 0x15d10 (writeSuccessTransactionsPostAt15d10Spec P))%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsWithdrawalsAdapter) := I.

Lemma write_success_transactions_data_handoff_parent
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  □ writeSuccessTransactionsDataWithdrawalsHandoff P -∗
  □ instr_pre 0x15668 (writeSuccessTransactionsPostAt15668DataSpec P) -∗
  □ instr_pre 0x15678 (writeSuccessTransactionsWithdrawalsAt15678Spec P).
Proof.
  iStartProof. iIntros "#Hhandoff #Hentry".
  iApply (write_success_transactions_data_withdrawals_handoff_pre P with
    "Hhandoff Hentry").
Qed.

Lemma write_success_transactions_data_provider_parent
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z)
    (transactions : list writeSuccessTransaction) (bytes : list (bv 8))
    (tail : spec) (remaining : nat) (first second : bv 64)
    (items : list ByteListItem) (total processed : nat)
    (prefix suffix : list (bv 8)) :
  □ writeSuccessTransactionsDataWithdrawalsProvider P -∗
  writeSuccessTransactionsLoopExitWithdrawalsData
    (writeSuccessTransactionsWithdrawalsLoopFrame P sp pointer base
      transactions bytes tail total processed remaining prefix suffix)
    sp pointer base transactions bytes tail (S remaining) first second items -∗
  ((bv_unsigned sp + 1120) ↦ₘ pointer ∗
   (bv_unsigned sp + 1128) ↦ₘ Z_to_bv 64 (Z.of_nat (S remaining)) ∗
   writeSuccessTransactionsWithdrawalsResources P sp pointer base total
     processed remaining bytes prefix suffix tail).
Proof.
  iStartProof. iIntros "#Hprovider Hdata".
  iEval (rewrite /writeSuccessTransactionsDataWithdrawalsProvider) in "Hprovider".
  iSpecialize ("Hprovider" $! sp pointer base transactions bytes tail remaining
    first second items total processed prefix suffix).
  iApply ("Hprovider" with "Hdata").
Qed.

Lemma write_success_transactions_to_withdrawals
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15c10 zesuEncoderByteListsCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ writeSuccessTransactionsWithdrawalsAdapter P -∗
  instr_body 0x15668 (writeSuccessTransactionsPostAt15668EventsSpec P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hmemcpy #Houtput #HbyteLists #Hint #Hadapter".
  iPoseProof (write_success_withdrawals_loop_pre P with
    "Hlookup Hcode Hmemcpy Hint Houtput") as "#Hwithdrawals".
  iPoseProof (write_success_transactions_post_1568c_withdrawals P with
    "Hlookup Hwithdrawals") as "H1568c".
  iEval (rewrite /writeSuccessTransactionsWithdrawalsAdapter) in "Hadapter".
  iPoseProof ("Hadapter" with "H1568c") as "H15d10".
  iApply (write_success_transactions_post_15668_events_to_1567c P with
    "Hlookup Hcode HbyteLists").
  iApply (write_success_transactions_post_1567c_load P with "Hlookup").
  iApply (write_success_transactions_post_15680_move P with "Hlookup").
  iApply (write_success_transactions_post_15684_auipc P with "Hlookup").
  iApply (write_success_transactions_post_15688_jump P with
    "Hlookup H15d10").
Qed.

Lemma write_success_transactions_to_withdrawals_pre
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15c10 zesuEncoderByteListsCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ writeSuccessTransactionsWithdrawalsAdapter P -∗
  □ instr_pre 0x15668 (writeSuccessTransactionsPostAt15668EventsSpec P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hmemcpy #Houtput #HbyteLists #Hint #Hadapter".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (write_success_transactions_to_withdrawals P with
    "Hlookup Hcode Hmemcpy Houtput HbyteLists Hint Hadapter").
Qed.

Lemma write_success_transactions_withdrawals_providers
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15c10 zesuEncoderByteListsCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  writeSuccessTransactionsLoopEventsCarrier P -∗
  □ writeSuccessTransactionsWithdrawalsAdapter P -∗
  (□ instr_pre 0x14f04 (writeSuccessTransactionsLoopEventsPostSpec P) ∗
   □ instr_pre 0x15668
     (writeSuccessTransactionsPostAt15668EventsSpec P))%I.
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hmemcpy #Houtput #HbyteLists #Hint Hcarrier
    #Hadapter".
  iSplitL "Hcarrier".
  - iApply (write_success_transactions_loop_events_carrier_parent P with
      "Hcarrier").
  - iApply (write_success_transactions_to_withdrawals_pre P with
      "Hlookup Hcode Hmemcpy Houtput HbyteLists Hint Hadapter").
Qed.
