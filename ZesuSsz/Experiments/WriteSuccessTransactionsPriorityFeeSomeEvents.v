Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.

Definition writeSuccessTransactionsPriorityFeeSomeBooleanTail
    (sp : bv 64) (transaction : writeSuccessTransaction)
    (remaining : list writeSuccessTransaction) (tail : spec) : spec :=
  writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
    (writeSuccessTransactionPhaseEvents TransactionGasLimit sp transaction
      (writeSuccessTransactionsEvents sp remaining tail)).

Global Typeclasses Opaque
  writeSuccessTransactionsPriorityFeeSomeBooleanTail.

Definition writeSuccessTransactionsPriorityFeeSomeBooleanEvents
    (sp : bv 64) (transaction : writeSuccessTransaction)
    (remaining : list writeSuccessTransaction) (tail : spec) : spec :=
  writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
    (writeSuccessTransactionsPriorityFeeSomeBooleanTail
      sp transaction remaining tail).

Global Typeclasses Opaque
  writeSuccessTransactionsPriorityFeeSomeBooleanEvents.
