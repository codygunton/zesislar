From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150f0.
Require Import ZesuSsz.Experiments.WriteSuccessTransactions10190CallerAdapter.
Require Import ZesuSsz.Experiments.WriteSuccessTransactions10190SavedAdapterA.
Require Import ZesuSsz.Experiments.WriteSuccessTransactions10190SavedAdapterB.

Import ListNotations.

Definition writeSuccessTransactions10190MachineFrame
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (base : Z)
    (transaction : writeSuccessTransaction)
    (transactions processed : list writeSuccessTransaction) : iProp Sigma :=
  (reg_col writeSuccessTransactions150e8OtherRegShapes ∗
   writeSuccessTransactionsScratch150e8
     sp base transactions processed transaction ∗ True)%I.

Global Typeclasses Opaque writeSuccessTransactions10190MachineFrame.

Lemma write_success_transactions_10190_machine_adapter
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (tail : spec) :
  zesu_c_call_ret 0
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
          (writeSuccessTransactionsEvents sp remaining tail)) ∗ True) -∗
  writeSuccessTransactions10190MachineFrame
    sp base transaction transactions processed -∗
  writeSuccessTransactionsMachine150f0
      sp base transactions processed transaction ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeSuccessTransactionPhaseEvents TransactionChainId sp transaction
        (writeSuccessTransactionsEvents sp remaining tail)) ∗ True.
Proof.
  iIntros "Hpost Hframe".
  rewrite /writeSuccessTransactions10190MachineFrame.
  iDestruct "Hframe" as "(Hother & Hscratch & _)".
  iEval (unfold zesu_c_call_ret) in "Hpost".
  iDestruct "Hpost" as "(HsysPost & Hcaller & Hsaved & Hrest)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hrest".
  iDestruct "Hrest" as (r10) "(H10Post & Hrest)".
  iDestruct "Hrest" as (b10) "(%Hr10 & Hrest)". subst r10.
  iDestruct "Hrest" as (r11) "(H11Post & Hrest)".
  iDestruct "Hrest" as (b11)
    "(%Hr11 & H2Post & Hstack & HmmioPost & HtracePost & _)". subst r11.
  iPoseProof (write_success_transactions_10190_caller_adapter b10 b11 with
    "Hcaller H10Post H11Post Hother") as "HcallerPost".
  iPoseProof (write_success_transactions_10190_saved_adapter_a transaction with
    "Hsaved") as
    "(H8Post & H9Post & H18Post & H19Post & H20Post & H21Post &
      HsavedTail & _)".
  iPoseProof (write_success_transactions_10190_saved_adapter_b transaction with
    "HsavedTail") as
    "(H22Post & H23Post & H24Post & H25Post & H26Post & H27Post & _)".
  rewrite /writeSuccessTransactionsMachine150f0.
  iFrame.
Qed.
