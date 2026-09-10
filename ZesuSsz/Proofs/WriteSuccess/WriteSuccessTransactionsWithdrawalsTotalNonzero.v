From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsWithdrawalsPayload.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsWithdrawalsTotalResources.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsSpec.

Lemma write_success_transactions_withdrawals_total_base_range
    (base : Z) (byteCount : nat) :
  (0x20000000 <= base)%Z ->
  (base + Z.of_nat byteCount < 0x40000000)%Z ->
  (0 <= base <= 2 ^ 64)%Z.
Proof.
  intros Hlower Hupper.
  have HbyteCount : (0 <= Z.of_nat byteCount)%Z := Nat2Z.is_nonneg byteCount.
  have HramUpper : (0x40000000 < 2 ^ 64)%Z by native_compute.
  lia.
Qed.

Lemma write_success_transactions_withdrawals_total_nonzero
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (remaining : nat)
    (bytes : list (bv 8)) (tail : spec) :
  (bv_unsigned sp + 1744) ↦ₘ? 48 -∗
  writeSuccessTransactionsWithdrawalsTotalResources P sp pointer base
    (S remaining) bytes tail -∗
  writeSuccessTransactionsWithdrawalsResources P sp pointer base
    (S remaining) 0 remaining bytes [] bytes tail.
Proof.
  iStartProof. iIntros "Hscratch Htotal".
  iEval (rewrite /writeSuccessTransactionsWithdrawalsTotalResources) in "Htotal".
  iDestruct "Htotal" as
    "(Hbytes & %Hpointer & %Hlength & %Hcount & %Halign & %Hlower & %Hupper &
      %HbaseLower & %HbaseUpper & Hexit & HP & _)".
  iAssert (writeSuccessWithdrawalsInvariant sp pointer base (S remaining) 0
    remaining bytes [] bytes)%I with "[]" as "Hinv".
  { iPureIntro. repeat split.
    - exact Hlength.
    - exact Hlength.
    - rewrite Z.mul_0_r Z.add_0_r. exact Hpointer.
    - exact Hcount.
    - exact Halign.
    - exact Hlower.
    - exact Hupper.
    - exact HbaseLower.
    - exact HbaseUpper. }
  iAssert (base ↦ₘ∗ ([] : list (bv 8)))%I with "[]" as "Hempty".
  { rewrite mem_mapsto_array_eq /mem_mapsto_array_def /=.
    iExists 1%N. iSplit; first done.
    iSplit; last done. iPureIntro.
    pose proof (write_success_transactions_withdrawals_total_base_range
      base (length bytes) HbaseLower HbaseUpper) as [HbaseNonnegative HbaseBound].
    split; first exact HbaseNonnegative.
    rewrite Z.mul_0_r Z.add_0_r. exact HbaseBound. }
  rewrite /writeSuccessTransactionsWithdrawalsResources.
  iFrame "Hscratch Hempty Hbytes Hinv Hexit HP".
Qed.
