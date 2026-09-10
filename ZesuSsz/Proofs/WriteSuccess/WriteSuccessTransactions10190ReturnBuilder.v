Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150ecCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150f0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactions10190MachineAdapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactions10190Return.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary10190Prepared.

Lemma write_success_transactions_10190_return_builder
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_body 0x150f0 (writeSuccessTransactionsAt150f0Spec P) -∗
  writeSuccessTransactions150ecCallFrame P sp base transaction
    transactions processed remaining bytes prefix suffix tail -∗
  writeSuccessTransactions10190ReturnBuilder
    sp base transaction transactions processed remaining tail.
Proof.
  iIntros "Hnext Hframe".
  rewrite /writeSuccessTransactions10190ReturnBuilder.
  iIntros "HreturnMachine".
  iApply (write_success_transactions_10190_return P sp base transaction
    transactions processed remaining bytes prefix suffix tail with "Hnext").
  rewrite /writeSuccessTransactions10190ReturnFrame.
  iFrame "HreturnMachine Hframe".
Qed.

Lemma write_success_transactions_10190_return_builder_apply
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (tail : spec) :
  writeSuccessTransactions10190ReturnBuilder
    sp base transaction transactions processed remaining tail -∗
  writeSuccessTransactions10190MachineFrame
    sp base transaction transactions processed -∗
  instr_pre 0x150f0
    (zesu_c_call_ret 0
      [RVal_Bits (writeSuccessTransactionWord transaction 192);
       RVal_Bits (writeSuccessTransactionWord transaction 16);
       RVal_Bits (writeSuccessTransactionWord transaction 48);
       RVal_Bits (writeSuccessTransactionWord transaction 224);
       RVal_Bits (writeSuccessTransactionWord transaction 56);
       RVal_Bits (writeSuccessTransactionWord transaction 72);
       RVal_Bits (writeSuccessTransactionWord transaction 200);
       RVal_Bits (writeSuccessTransactionWord transaction 24);
       RVal_Bits (writeSuccessTransactionWord transaction 8);
       RVal_Bits (writeSuccessTransactionWord transaction 0);
       RVal_Bits (writeSuccessTransactionWord transaction 184);
       RVal_Bits
         (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32))]
      (BV 64 0x150f0) sp
      (fun _ =>
        mmio_range 0x2401a0c0 16 ∗
        spec_trace
          (writeSuccessTransactionPhaseEvents TransactionChainId sp transaction
            (writeSuccessTransactionsEvents sp remaining tail)) ∗ True)).
Proof.
  rewrite /writeSuccessTransactions10190ReturnBuilder.
  iIntros "Hbuilder Hmachine".
  iApply ("Hbuilder" with "Hmachine").
Qed.
