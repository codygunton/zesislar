Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanCallRet.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanAbiTail.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanAbiIntro.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanAbiFinalize.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanReturn.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanRegisters.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

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
