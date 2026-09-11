Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674Boundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPuncturedScratch.

(** This is the transaction frame while the byte-lists callee owns its
    80-byte call stack.  The two decoded withdrawals words stay separate. *)
Definition writeSuccessTransactionsPost15674DataCallFrame
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (base : Z) (total : nat)
    (first second pointer remaining : bv 64) (items : list ByteListItem) :
    iProp Sigma :=
  ((bv_unsigned sp) ↦ₘ? 104 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
   (bv_unsigned sp + 120) ↦ₘ? 984 ∗
   (bv_unsigned sp + 1104) ↦ₘ first ∗
   (bv_unsigned sp + 1112) ↦ₘ second ∗
   (bv_unsigned sp + 1120) ↦ₘ pointer ∗
   (bv_unsigned sp + 1128) ↦ₘ remaining ∗
   (bv_unsigned sp + 1136) ↦ₘ? 608 ∗
   (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   (bv_unsigned sp + 1792) ↦ₘ? 104 ∗
   byteListItemResources (bv_unsigned first) items ∗
   ⌜writeSuccessTransactionsPost15674ByteListFacts sp first second items⌝)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost15674DataCallFrame) := I.

Lemma write_success_transactions_post_15674_data_call_frame_enter
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (base : Z) (total : nat)
    (first second pointer remaining : bv 64) (items : list ByteListItem) :
  writeSuccessTransactionsPuncturedScratch sp base total -∗
  writeSuccessTransactionsLoopCarrierPayload sp first second pointer remaining
    items -∗
  (bv_unsigned sp + 1744) ↦ₘ? 48 -∗
  (bv_unsigned sp - 80) ↦ₘ? 80 ∗
  writeSuccessTransactionsPost15674DataCallFrame sp base total first second
    pointer remaining items.
Proof.
  iIntros "Hscratch Hcarrier Hwithdrawals".
  iEval (rewrite /writeSuccessTransactionsPuncturedScratch) in "Hscratch".
  iDestruct "Hscratch" as
    "(Hlower & Hbase & Htotal & Hprefix & Hmiddle & Htail & _)".
  iEval (rewrite /writeSuccessTransactionsLoopCarrierPayload
    /writeSuccessTransactionsWordsCarrier) in "Hcarrier".
  iDestruct "Hcarrier" as
    "((Hfirst & Hsecond & Hpointer & Hremaining) & HcallStack & Hitems & Hfacts)".
  iDestruct (mem_mapsto_uninit_split 48 with "Hlower") as
    "(Hlower48 & Hlower104)"; first lia.
  have HlowerAddress : bv_unsigned sp - 48 + 48 = bv_unsigned sp by lia.
  iEval (rewrite HlowerAddress) in "Hlower104".
  iAssert ((bv_unsigned sp - 80) ↦ₘ? 80)%I
    with "[HcallStack Hlower48]" as "Hstack80".
  { iApply (mem_mapsto_uninit_combine 32 with "HcallStack"); first lia.
    have Haddress : bv_unsigned sp - 80 + 32 = bv_unsigned sp - 48 by lia.
    iEval (rewrite -Haddress) in "Hlower48".
    iExact "Hlower48". }
  iSplitL "Hstack80"; first iExact "Hstack80".
  iEval (rewrite /writeSuccessTransactionsPost15674DataCallFrame).
  iFrame "Hlower104 Hbase Htotal Hprefix Hfirst Hsecond Hpointer Hremaining Hmiddle
    Hwithdrawals Htail Hitems Hfacts".
Qed.

Lemma write_success_transactions_post_15674_data_call_frame_exit
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (base : Z) (total : nat)
    (first second pointer remaining : bv 64) (items : list ByteListItem) :
  (bv_unsigned sp - 80) ↦ₘ? 80 -∗
  writeSuccessTransactionsPost15674DataCallFrame sp base total first second
    pointer remaining items -∗
  writeSuccessTransactionsPuncturedScratch sp base total ∗
  writeSuccessTransactionsLoopCarrierPayload sp first second pointer remaining
    items ∗
  (bv_unsigned sp + 1744) ↦ₘ? 48.
Proof.
  iIntros "Hstack80 Hframe".
  iEval (rewrite /writeSuccessTransactionsPost15674DataCallFrame) in "Hframe".
  iDestruct "Hframe" as
    "(Hlower104 & Hbase & Htotal & Hprefix & Hfirst & Hsecond & Hpointer & Hremaining & Hmiddle &
      Hwithdrawals & Htail & Hitems & Hfacts)".
  iDestruct (mem_mapsto_uninit_split 32 with "Hstack80") as
    "(HcallStack & Hlower48)"; first lia.
  have Haddress : bv_unsigned sp - 80 + 32 = bv_unsigned sp - 48 by lia.
  iEval (rewrite Haddress) in "Hlower48".
  have HlowerAddress : bv_unsigned sp - 48 + 48 = bv_unsigned sp by lia.
  iEval (rewrite -HlowerAddress) in "Hlower104".
  iAssert ((bv_unsigned sp - 48) ↦ₘ? 152)%I
    with "[Hlower48 Hlower104]" as "Hlower".
  { iApply (mem_mapsto_uninit_combine 48 with "Hlower48"); first lia.
    iExact "Hlower104". }
  iSplitL "Hlower Hbase Htotal Hprefix Hmiddle Htail".
  { iEval (rewrite /writeSuccessTransactionsPuncturedScratch).
    iFrame. }
  iSplitL "Hfirst Hsecond Hpointer Hremaining HcallStack Hitems Hfacts".
  { iEval (rewrite /writeSuccessTransactionsLoopCarrierPayload
      /writeSuccessTransactionsWordsCarrier).
    iFrame "Hfirst Hsecond Hpointer Hremaining HcallStack Hitems Hfacts".
  }
  iExact "Hwithdrawals".
Qed.
