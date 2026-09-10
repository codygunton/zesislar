Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanAbiTail.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanRegisters.

Lemma write_success_transactions_priority_fee_boolean_abi_intro
    `{!islaG Sigma} `{!threadG}
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (remaining : list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (sp : bv 64) (tail : spec) :
  writeSuccessTransactionsPriorityFeeBooleanRegisters
      transaction sp (BV 64 0x15148) -∗
  writeSuccessTransactionsPriorityFeeBooleanAbiTail
      sp transaction remaining tail -∗
  writeSuccessTransactionsPriorityFeeBooleanAbiRegisters transaction sp (BV 64 0x15148)
    (writeSuccessTransactionsPriorityFeeBooleanAbiTail
      sp transaction remaining tail).
Proof.
  iStartProof. iIntros "Hregs Htail".
  iApply (write_success_transactions_priority_fee_boolean_registers
    transaction sp (BV 64 0x15148)
    (writeSuccessTransactionsPriorityFeeBooleanAbiTail
      sp transaction remaining tail)).
  iFrame.
Qed.
