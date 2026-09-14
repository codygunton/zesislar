Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessStorageKeysSpec WriteSuccessAccessListsSpec
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsFlagLoads
  WriteSuccessExactTransactionsSourceFieldLayout WriteSuccessExactTransactionsSourceBlobFeeFrame.

Definition transactionSourceAuthorizationBorrowed `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (index : nat) (authBytes : list (bv 8)) : iProp Sigma :=
  (reg_col [(KindReg "x8", BitsShape 64); (KindReg "x9", BitsShape 64)] ∗
   reg_col [(KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
     (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
   writeSuccessByteArrayOwn (transactionRowWord bytes index 240) authBytes ∗
   (bv_unsigned sp + 1744) ↦ₘ? 144 ∗ (bv_unsigned sp - 48) ↦ₘ? 16 ∗
   (bv_unsigned sp + 168) ↦ₘ transactionRowWord bytes index 240 ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSourceAuthorizationBorrowed) := I.

Definition transactionSourceAuthorizationLoan `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (bytes : list (bv 8)) (processed index : nat)
    (dataBytes accessBytes chainBytes : list (bv 8)) (entries : list writeSuccessAccessEntry)
    (blobBytes authBytes : list (bv 8)) (Q : iProp Sigma) : iProp Sigma :=
  (transactionSourceAuthorizationBorrowed sp bytes index authBytes -∗
   transactionSourceBlobFeeRetained sp base bytes processed index dataBytes accessBytes
     chainBytes entries blobBytes
     (writeSuccessByteArrayOwn (transactionRowWord bytes index 240) authBytes ∗ Q)%I)%I.
Global Instance : LithiumUnfold (@transactionSourceAuthorizationLoan) := I.


Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.IslarisMachine.
Definition transactionSourceAuthorizationExit `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (bytes : list (bv 8)) (processed index : nat)
    (dataBytes accessBytes chainBytes : list (bv 8)) (entries : list writeSuccessAccessEntry)
    (blobBytes authBytes : list (bv 8)) (tail : spec) (Q : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   reg_col [(KindReg "x1", BitsShape 64); (KindReg "x5", BitsShape 64);
     (KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64)] ∗
   "x18" ↦ᵣ RVal_Bits (BV 64 0) ∗ (bv_unsigned sp - 32) ↦ₘ? 32 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗
   (bv_unsigned sp + 144) ↦ₘ transactionRowWord bytes index 88 ∗
   (bv_unsigned sp + 152) ↦ₘ transactionRowWord bytes index 80 ∗
   (bv_unsigned sp + 160) ↦ₘ transactionRowWord bytes index 248 ∗
   transactionSourceBlobFeeRetained sp base bytes processed index dataBytes accessBytes
     chainBytes entries blobBytes
     (writeSuccessByteArrayOwn (transactionRowWord bytes index 240) authBytes ∗ Q)%I ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSourceAuthorizationExit) := I.
