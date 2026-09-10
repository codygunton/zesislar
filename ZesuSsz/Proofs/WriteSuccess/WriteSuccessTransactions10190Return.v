From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150ecCall.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150f0.
Require Import ZesuSsz.Experiments.WriteSuccessTransactions10190MachineAdapter.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Definition writeSuccessTransactions10190ReturnFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
  (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (writeSuccessTransactions10190MachineFrame
     sp base transaction transactions processed ∗
   writeSuccessTransactions150ecCallFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗ True)%I.

Global Typeclasses Opaque writeSuccessTransactions10190ReturnFrame.

Lemma write_success_transactions_10190_return
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_body 0x150f0 (writeSuccessTransactionsAt150f0Spec P) -∗
  writeSuccessTransactions10190ReturnFrame P sp base transaction transactions
    processed remaining bytes prefix suffix tail -∗
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
  iIntros "Hnext Hframe".
  rewrite /writeSuccessTransactions10190ReturnFrame.
  iDestruct "Hframe" as "(HmachineFrame & Hframe & _)".
  iApply instr_pre_to_body. iNext.
  iApply (instr_pre_wand 0x150f0 0x150f0 false false with "Hnext");
    [done | done |].
  iIntros "Hpost".
  iPoseProof (write_success_transactions_10190_machine_adapter sp base
    transaction transactions processed remaining tail with
    "Hpost HmachineFrame") as
    "(Hmachine & Hmmio & Htrace & _)".
  iEval (unfold writeSuccessTransactions150ecCallFrame) in "Hframe".
  iDestruct "Hframe" as
    "(Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining & HP &
      Hinvariant & Hexit & _)".
  rewrite /writeSuccessTransactionsAt150f0Spec
    /writeSuccessTransactionPhaseHandoff.
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  rewrite /writeSuccessTransactionsProcessedOwn.
  iFrame.
Qed.
