Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessStorageKeysSpec WriteSuccessAccessListsSpec
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsFlagLoads
  WriteSuccessExactTransactionsSourceFieldLayout WriteSuccessExactTransactionsSourceBlobFeeFrame.

Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSourceAuthorizationSpec.

Definition transactionSourceAuthorizationZeroFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (bytes : list (bv 8)) (processed index : nat)
    (dataBytes accessBytes chainBytes : list (bv 8)) (entries : list writeSuccessAccessEntry)
    (blobBytes : list (bv 8)) (Q : iProp Sigma) : iProp Sigma :=
  (reg_col [(KindReg "x1", BitsShape 64); (KindReg "x5", BitsShape 64);
      (KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64)] ∗
   reg_col [(KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
      (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
   (bv_unsigned sp + 1744) ↦ₘ? 144 ∗ (bv_unsigned sp - 48) ↦ₘ? 16 ∗
   (bv_unsigned sp - 32) ↦ₘ? 32 ∗
   (bv_unsigned sp + 144) ↦ₘ transactionRowWord bytes index 88 ∗
   (bv_unsigned sp + 152) ↦ₘ transactionRowWord bytes index 80 ∗
   (bv_unsigned sp + 160) ↦ₘ transactionRowWord bytes index 248 ∗
   transactionSourceAuthorizationLoan sp base bytes processed index dataBytes accessBytes
     chainBytes entries blobBytes [] Q ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSourceAuthorizationZeroFrame) := I.
