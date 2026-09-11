Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome1517cBoundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome15170Handoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Definition writeSuccessTransactionsOptionalAddressSome15190Frame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)] ∗
   writeSuccessTransactionsScratch15174
     sp base transactions processed transaction ∗
   writeSuccessTransactionsOptionalAddressSomeFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsOptionalAddressSome15190Frame) := I.

Definition writeSuccessTransactionsOptionalAddressSomeAt15190Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
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
      (BV 64 0x15190) sp
      (fun _ =>
        mmio_range 0x2401a0c0 16 ∗
        spec_trace
          (writeSuccessTransactionPhaseEvents TransactionValue sp transaction
            (writeSuccessTransactionsEvents sp remaining tail)) ∗
        writeSuccessTransactionsOptionalAddressSome15190Frame P sp base
          transaction transactions processed remaining bytes prefix suffix tail))%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsOptionalAddressSomeAt15190Spec) := I.
