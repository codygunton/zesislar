Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeBooleanCallRet.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeBooleanAbiTail.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeBooleanAbiIntro.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeBooleanAbiFinalize.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeBooleanReturn.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeBooleanRegisters.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.

Lemma write_success_transactions_priority_fee_boolean_assemble
    `{!islaG Sigma} `{!threadG}
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (remaining : list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (sp : bv 64) (tail : spec) :
  writeSuccessTransactionsPriorityFeeBooleanRegisters
      transaction sp (BV 64 0x15148) -∗
  writeSuccessTransactionsPriorityFeeBooleanAbiTail
    sp transaction remaining tail -∗
  zesuEncoderBooleanCallSpec.
Proof.
  iStartProof. iIntros "Hregs Htail".
  iPoseProof (write_success_transactions_priority_fee_boolean_abi_intro
    transaction remaining sp tail with "Hregs Htail") as "Habi".
  iApply (write_success_transactions_priority_fee_boolean_abi_finalize
    transaction remaining sp tail with "Habi").
Qed.
