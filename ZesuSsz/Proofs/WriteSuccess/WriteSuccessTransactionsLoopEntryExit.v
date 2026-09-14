Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Lemma write_success_transactions_loop_exit_remaining_nil
    (processed remaining : list writeSuccessTransaction)
    (Hbound : (length (processed ++ remaining) < 2 ^ 64)%nat)
    (Heq : Z_to_bv 64 (Z.of_nat (length processed)) =
      Z_to_bv 64 (Z.of_nat (length (processed ++ remaining)))) :
  remaining = [].
Proof.
  have HprocessedLe :
      (length processed <= length (processed ++ remaining))%nat.
  { rewrite app_length. lia. }
  have HprocessedBound : (length processed < 2 ^ 64)%nat.
  { exact (Nat.le_lt_trans _ _ _ HprocessedLe Hbound). }
  have HprocessedRange :
      (0 <= Z.of_nat (length processed) < bv_modulus 64)%Z.
  { split; [lia |].
    change (Z.of_nat (length processed) < 2 ^ 64)%Z.
    have Hz := (proj1 (Nat2Z.inj_lt _ _) HprocessedBound).
    rewrite Nat2Z.inj_pow in Hz. exact Hz. }
  have HtotalRange :
      (0 <= Z.of_nat (length (processed ++ remaining)) < bv_modulus 64)%Z.
  { split; [lia |].
    change (Z.of_nat (length (processed ++ remaining)) < 2 ^ 64)%Z.
    have Hz := (proj1 (Nat2Z.inj_lt _ _) Hbound).
    rewrite Nat2Z.inj_pow in Hz. exact Hz. }
  have Hunsigned := f_equal bv_unsigned Heq.
  rewrite !Z_to_bv_unsigned in Hunsigned.
  rewrite !bv_wrap_small in Hunsigned; [|exact HtotalRange|exact HprocessedRange].
  have HremainingLength : length remaining = 0%nat.
  { rewrite app_length in Hunsigned. lia. }
  exact (proj1 (length_zero_iff_nil remaining) HremainingLength).
Qed.

Definition writeSuccessTransactionsLoopExitBranchFrame `{!islaG Sigma}
    `{!threadG} (P : iProp Sigma) (sp : bv 64) (base : Z)
    (processed remaining : list writeSuccessTransaction) (tail : spec) :
    iProp Sigma :=
  ((base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      writeSuccessTransactionsBytes remaining ∗
   writeSuccessTransactionsOwn processed ∗
   writeSuccessTransactionsOwn remaining ∗
   (bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ
      Z_to_bv 64 (Z.of_nat (length (processed ++ remaining))) ∗
   (bv_unsigned sp + 120) ↦ₘ? 1776 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessTransactionsEvents sp remaining tail) ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsLoopExitBranchFrame) := I.

Lemma write_success_transactions_loop_entry_exit
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) (sp : bv 64) (base : Z)
    (processed remaining : list writeSuccessTransaction) (tail : spec)
    (Hbound : (length (processed ++ remaining) < 2 ^ 64)%nat)
    (Heq : Z_to_bv 64 (Z.of_nat (length processed)) =
      Z_to_bv 64 (Z.of_nat (length (processed ++ remaining)))) :
  writeSuccessTransactionsLoopExitBranchFrame
      P sp base processed remaining tail -∗
  writeSuccessTransactionsOwn (processed ++ remaining) ∗
  writeSuccessTransactionsScratch sp base (length (processed ++ remaining)) ∗
  mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ P ∗ True.
Proof.
  iIntros "Hframe".
  have Hnil := write_success_transactions_loop_exit_remaining_nil
    processed remaining Hbound Heq.
  subst remaining. rewrite app_nil_r.
  iDestruct "Hframe" as
    "(_ & Hprocessed & _ & Hlower & Hbase & Htotal & Hupper & Hmmio & Htail & HP & _)".
  iEval (rewrite app_nil_r) in "Htotal".
  rewrite /writeSuccessTransactionsScratch.
  iFrame "Hprocessed Hlower Hbase Htotal Hupper Hmmio Htail HP".
Qed.
