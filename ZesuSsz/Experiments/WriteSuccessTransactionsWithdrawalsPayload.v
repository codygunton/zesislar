From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessValueBlock.

(** The decoded value words at stack offsets 1120 and 1128 are values 11 and
    12.  This payload gives those words their withdrawals interpretation. *)
Definition writeSuccessTransactionsWithdrawalsPayload
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  ((bv_unsigned sp + 1120) ↦ₘ pointer ∗
   (bv_unsigned sp + 1128) ↦ₘ
     Z_to_bv 64 (Z.of_nat (S remaining)) ∗
   (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   base ↦ₘ∗ prefix ∗ bv_unsigned pointer ↦ₘ∗ suffix ∗
   writeSuccessWithdrawalsInvariant sp pointer base total processed remaining
     bytes prefix suffix ∗
   instr_pre 0x156e8
     (writeSuccessWithdrawalsLoopExit sp base total bytes tail P) ∗ P ∗
   True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsWithdrawalsPayload) := I.

(** The loop carrier owns the two decoded words.  This separate frame owns the
    remaining linear resources, so the loop does not duplicate memory. *)
Definition writeSuccessTransactionsWithdrawalsResources
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  ((bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   base ↦ₘ∗ prefix ∗ bv_unsigned pointer ↦ₘ∗ suffix ∗
   writeSuccessWithdrawalsInvariant sp pointer base total processed remaining
     bytes prefix suffix ∗
   instr_pre 0x156e8
     (writeSuccessWithdrawalsLoopExit sp base total bytes tail P) ∗ P ∗
   True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsWithdrawalsResources) := I.

Lemma write_success_transactions_withdrawals_payload_combine
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  (bv_unsigned sp + 1120) ↦ₘ pointer -∗
  (bv_unsigned sp + 1128) ↦ₘ
    Z_to_bv 64 (Z.of_nat (S remaining)) -∗
  writeSuccessTransactionsWithdrawalsResources P sp pointer base total
    processed remaining bytes prefix suffix tail -∗
  writeSuccessTransactionsWithdrawalsPayload P sp pointer base total processed
    remaining bytes prefix suffix tail.
Proof.
  iIntros "Hpointer Hcount Hresources".
  rewrite /writeSuccessTransactionsWithdrawalsResources
    /writeSuccessTransactionsWithdrawalsPayload.
  iFrame.
Qed.

Lemma write_success_transactions_withdrawals_value_word_11
    (values : list (bv 64)) :
  writeSuccessValueWord values 11 = default (BV 64 0) (values !! 11%nat).
Proof. reflexivity. Qed.

Lemma write_success_transactions_withdrawals_value_word_12
    (values : list (bv 64)) :
  writeSuccessValueWord values 12 = default (BV 64 0) (values !! 12%nat).
Proof. reflexivity. Qed.
