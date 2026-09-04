Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeSomeBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeSomeEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeBooleanReturn.

Definition writeSuccessTransactionsPriorityFeeSomeBooleanMmio
    `{!islaG Sigma} `{!threadG} (_ : list (bv 64)) : iProp Sigma :=
  mmio_range 0x2401a0c0 16.

Definition writeSuccessTransactionsPriorityFeeSomeBooleanTrace
    `{!islaG Sigma} `{!threadG} (sp : bv 64)
    (transaction : writeSuccessTransaction)
    (remaining : list writeSuccessTransaction) (tail : spec)
    (_ : list (bv 64)) : iProp Sigma :=
  spec_trace
    (writeSuccessTransactionsPriorityFeeSomeBooleanTail
      sp transaction remaining tail).

Global Typeclasses Opaque writeSuccessTransactionsPriorityFeeSomeBooleanMmio.
Global Typeclasses Opaque writeSuccessTransactionsPriorityFeeSomeBooleanTrace.

Definition writeSuccessTransactionsPriorityFeeSomeBooleanCallRet
    `{!islaG Sigma} `{!threadG} (sp : bv 64)
    (transaction : writeSuccessTransaction)
    (remaining : list writeSuccessTransaction) (tail : spec) : iProp Sigma :=
  zesu_c_call_ret 16
    (writeSuccessTransactionsPriorityFeeSavedValues transaction)
    (BV 64 0x15128) sp
    (fun args =>
      writeSuccessTransactionsPriorityFeeSomeBooleanMmio args ∗
      writeSuccessTransactionsPriorityFeeSomeBooleanTrace
        sp transaction remaining tail args ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsPriorityFeeSomeBooleanCallRet) := I.
