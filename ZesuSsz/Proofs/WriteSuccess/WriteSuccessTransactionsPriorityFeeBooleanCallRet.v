Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanReturn.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Definition writeSuccessTransactionsPriorityFeeBooleanMmio
    `{!islaG Sigma} `{!threadG} (sp : bv 64)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (remaining : list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (tail : spec) (_ : list (bv 64)) : iProp Sigma :=
  mmio_range 0x2401a0c0 16.

Definition writeSuccessTransactionsPriorityFeeBooleanTrace
    `{!islaG Sigma} `{!threadG} (sp : bv 64)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (remaining : list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (tail : spec) (_ : list (bv 64)) : iProp Sigma :=
  spec_trace
    (writeSuccessTransactionPhaseEvents TransactionGasLimit sp transaction
      (writeSuccessTransactionsEvents sp remaining tail)).

Global Typeclasses Opaque writeSuccessTransactionsPriorityFeeBooleanMmio.
Global Typeclasses Opaque writeSuccessTransactionsPriorityFeeBooleanTrace.

Definition writeSuccessTransactionsPriorityFeeBooleanCallRet
    `{!islaG Sigma} `{!threadG} (sp : bv 64)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (remaining : list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (tail : spec) : iProp Sigma :=
  zesu_c_call_ret 16
    (writeSuccessTransactionsPriorityFeeSavedValues transaction)
    (BV 64 0x15148) sp
    (fun args =>
      writeSuccessTransactionsPriorityFeeBooleanMmio
        sp transaction remaining tail args ∗
      writeSuccessTransactionsPriorityFeeBooleanTrace
        sp transaction remaining tail args ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsPriorityFeeBooleanCallRet) := I.
