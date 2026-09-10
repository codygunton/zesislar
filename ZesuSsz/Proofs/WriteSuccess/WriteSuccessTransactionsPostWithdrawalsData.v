Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost1568cWithdrawals.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPuncturedScratch.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsWithdrawalsPayload.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsWithdrawalsTail.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsWithdrawalsTailState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsSpec.

(** This is the exact transaction exit state before the byte-lists call. *)
Definition writeSuccessTransactionsPostAt15668DataSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (transactions : list writeSuccessTransaction) (bytes : list (bv 8))
      (tail : spec) (count : nat) (first second : bv 64)
      (items : list ByteListItem),
    writeSuccessTransactionsLoopExitWithdrawalsData P sp pointer base
      transactions bytes tail count first second items)%I.

(** The source theorem for this contract must preserve both decoded words and
    provide all withdrawals resources at the byte-lists return point. *)
Definition writeSuccessTransactionsDataWithdrawalsHandoff
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (□ instr_pre 0x15668 (writeSuccessTransactionsPostAt15668DataSpec P) -∗
   □ instr_pre 0x15678 (writeSuccessTransactionsWithdrawalsAt15678Spec P))%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPostAt15668DataSpec) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsDataWithdrawalsHandoff) := I.

(** This frame carries the withdrawals state through the transaction loop.
    The final wand consumes the transaction resources after byte-list output. *)
Definition writeSuccessTransactionsWithdrawalsLoopFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z)
    (transactions : list writeSuccessTransaction) (bytes : list (bv 8))
    (tail : spec) (total processed remaining : nat)
    (prefix suffix : list (bv 8)) : iProp Sigma :=
  (base ↦ₘ∗ prefix ∗ bv_unsigned pointer ↦ₘ∗ suffix ∗
   writeSuccessWithdrawalsInvariant sp pointer base total processed remaining
     bytes prefix suffix ∗
   instr_pre 0x156e8
     (writeSuccessWithdrawalsLoopExit sp base total bytes tail P) ∗
   (base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions -∗ P))%I.

(** This is the only upstream contract needed after the transaction loop. *)
Definition writeSuccessTransactionsDataWithdrawalsProvider
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (□ ∀ (sp pointer : bv 64) (base : Z)
      (transactions : list writeSuccessTransaction) (bytes : list (bv 8))
      (tail : spec) (remaining : nat) (first second : bv 64)
      (items : list ByteListItem) (total processed : nat)
      (prefix suffix : list (bv 8)),
    writeSuccessTransactionsLoopExitWithdrawalsData
      (writeSuccessTransactionsWithdrawalsLoopFrame P sp pointer base
        transactions bytes tail total processed remaining prefix suffix)
      sp pointer base transactions bytes tail (S remaining) first second items -∗
    ((bv_unsigned sp + 1120) ↦ₘ pointer ∗
     (bv_unsigned sp + 1128) ↦ₘ Z_to_bv 64 (Z.of_nat (S remaining)) ∗
     writeSuccessTransactionsWithdrawalsResources P sp pointer base total
       processed remaining bytes prefix suffix tail))%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsWithdrawalsLoopFrame) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsDataWithdrawalsProvider) := I.

(** This is the only remaining native source theorem.  It executes the
    byte-lists path after the provider has supplied its complete frame. *)
Definition writeSuccessTransactionsPost15668To15678WithdrawalsDataSource
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (□ ∀ (sp pointer : bv 64) (base : Z)
      (transactions : list writeSuccessTransaction) (bytes : list (bv 8))
      (tail : spec) (remaining : nat) (first second : bv 64)
      (items : list ByteListItem) (total processed : nat)
      (prefix suffix : list (bv 8)),
    instr_pre 0x15668
      (writeSuccessTransactionsPostAt15668DataSpec
        (writeSuccessTransactionsWithdrawalsLoopFrame P sp pointer base
          transactions bytes tail total processed remaining prefix suffix)) -∗
    instr_pre 0x15678 (writeSuccessTransactionsWithdrawalsAt15678Spec P))%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost15668To15678WithdrawalsDataSource) := I.

Lemma write_success_transactions_data_withdrawals_provider
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  ⊢ writeSuccessTransactionsDataWithdrawalsProvider P.
Proof.
  iStartProof. iModIntro.
  iIntros (sp pointer base transactions bytes tail remaining first second items
    total processed prefix suffix) "Hdata".
  iEval (rewrite /writeSuccessTransactionsLoopExitWithdrawalsData
    /writeSuccessTransactionsLoopExitEventsData) in "Hdata".
  iDestruct "Hdata" as
    "(Hsys & Hother & H2 & H10 & H11 & Hbytes & Hown & Hscratch & Hcarrier &
      Hwithdrawals & Hmmio & Htrace & %Halign16 & %Halign8 & %Hlow & %Hhigh &
      Hframe & _)".
  iEval (rewrite /writeSuccessTransactionsLoopCarrierPayload
    /writeSuccessTransactionsWordsCarrier) in "Hcarrier".
  iDestruct "Hcarrier" as
    "((Hfirst & Hsecond & Hpointer & Hremaining) & HcallStack & Hitems & Hfacts)".
  iEval (rewrite /writeSuccessTransactionsWithdrawalsLoopFrame) in "Hframe".
  iDestruct "Hframe" as "(Hprefix & Hsuffix & Hinv & Hexit & Hfinish)".
  iPoseProof ("Hfinish" with "[Hbytes Hown]") as "HP".
  { iFrame. }
  iEval (rewrite /writeSuccessTransactionsWithdrawalsResources).
  iFrame "Hpointer Hremaining Hwithdrawals Hprefix Hsuffix Hinv Hexit HP".
Qed.

Lemma write_success_transactions_data_withdrawals_handoff_pre
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  □ writeSuccessTransactionsDataWithdrawalsHandoff P -∗
  □ instr_pre 0x15668 (writeSuccessTransactionsPostAt15668DataSpec P) -∗
  □ instr_pre 0x15678 (writeSuccessTransactionsWithdrawalsAt15678Spec P).
Proof.
  iStartProof. iIntros "#Hhandoff #Hentry".
  iEval (rewrite /writeSuccessTransactionsDataWithdrawalsHandoff) in "Hhandoff".
  iApply ("Hhandoff" with "Hentry").
Qed.

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
