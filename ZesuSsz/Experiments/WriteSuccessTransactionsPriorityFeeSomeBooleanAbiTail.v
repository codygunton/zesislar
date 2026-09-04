Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeSomeEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeSomeBooleanCallRet.

Definition writeSuccessTransactionsPriorityFeeSomeBooleanAbiTail
    `{!islaG Sigma} `{!threadG} (sp : bv 64)
    (transaction : writeSuccessTransaction)
    (remaining : list writeSuccessTransaction) (tail : spec) : iProp Sigma :=
  (⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜bv_extract 0 1 (BV 64 0x15128) = BV 1 0⌝ ∗
   ⌜bv_extract 1 1 (BV 64 0x15128) = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 (BV 64 0x15128) = BV 2 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 16 /\
     bv_unsigned sp < 0x40000000⌝ ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace
     (writeSuccessTransactionsPriorityFeeSomeBooleanEvents
       sp transaction remaining tail) ∗
   instr_pre 0x15128
     (writeSuccessTransactionsPriorityFeeSomeBooleanCallRet
       sp transaction remaining tail))%I.

Global Typeclasses Opaque writeSuccessTransactionsPriorityFeeSomeBooleanAbiTail.

Lemma write_success_transactions_priority_fee_some_boolean_abi_tail
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (transaction : writeSuccessTransaction)
    (remaining : list writeSuccessTransaction) (tail : spec)
    (Halign : bv_unsigned sp `mod` 16 = 0)
    (Hlower : 0x20000000 <= bv_unsigned sp - 16)
    (Hupper : bv_unsigned sp < 0x40000000) :
  (bv_unsigned sp - 16) ↦ₘ? 16 -∗
  mmio_range 0x2401a0c0 16 -∗
  spec_trace
    (writeSuccessTransactionsPriorityFeeSomeBooleanEvents
      sp transaction remaining tail) -∗
  instr_pre 0x15128
    (writeSuccessTransactionsPriorityFeeSomeBooleanCallRet
      sp transaction remaining tail) -∗
  writeSuccessTransactionsPriorityFeeSomeBooleanAbiTail
    sp transaction remaining tail.
Proof.
  iIntros "Hstack Hmmio Htrace Hret".
  rewrite /writeSuccessTransactionsPriorityFeeSomeBooleanAbiTail.
  iFrame.
  repeat iSplit; try iPureIntro; try assumption; try native_compute;
    try bv_solve; try lia; done.
Qed.
