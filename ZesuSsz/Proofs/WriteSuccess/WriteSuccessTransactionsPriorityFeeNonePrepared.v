From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeCore.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeFrameBounds.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeMachineAdapter.

Definition writeSuccessTransactionsPriorityFeeNonePreparedSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionsPriorityFeeMachineParts P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
        (writeSuccessTransactionPhaseEvents TransactionGasLimit sp transaction
          (writeSuccessTransactionsEvents sp remaining tail))) ∗
    writeSuccessTransactionsPriorityFeeFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsPriorityFeeNonePreparedSpec) := I.

Lemma write_success_transactions_priority_fee_none_prepare
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessTransactionsPriorityFeeNoneCoreSpec P -∗
  writeSuccessTransactionsPriorityFeeNonePreparedSpec P.
Proof.
  iIntros "(%sp & %base & %transaction & %transactions & %processed &
    %remaining & %bytes & %prefix & %suffix & %tail & Hmachine & Hmmio &
    Htrace & Hframe & _)".
  iPoseProof (write_success_transactions_priority_fee_machine_split P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    with "Hmachine") as "Hmachine".
  iPoseProof (write_success_transactions_priority_fee_frame_bounds P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    with "Hframe") as "(Hframe & %Halign & %Hlower & %Hupper)".
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iFrame. repeat iSplit; try iPureIntro; try assumption; try done.
Qed.
