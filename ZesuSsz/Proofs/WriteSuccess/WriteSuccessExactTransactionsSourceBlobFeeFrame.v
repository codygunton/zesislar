Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessAccessListsSpec WriteSuccessStorageKeysSpec
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsFlagLoads
  WriteSuccessExactBlobHashesAuthorizationEntry
  WriteSuccessExactTransactionsSourceFieldLayout.

Definition transactionSourceBlobFeeRetained `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (bytes : list (bv 8)) (processed index : nat)
    (dataBytes accessBytes chainBytes : list (bv 8))
    (entries : list writeSuccessAccessEntry) (blobBytes : list (bv 8))
    (Q : iProp Sigma) : iProp Sigma :=
  (∃ pointer storedIndex : bv 64,
   "x19" ↦ᵣ RVal_Bits pointer ∗ "x22" ↦ᵣ RVal_Bits (BV 64 0) ∗
   reg_col blobAuthorizationRemainingShapes ∗
   writeSuccessByteArrayOwn (transactionRowWord bytes index 224) blobBytes ∗
   (bv_unsigned sp + 136) ↦ₘ transactionRowWord bytes index 232 ∗
   bv_unsigned (transactionRowWord bytes index 208) ↦ₘ∗ accessBytes ∗
   writeSuccessAccessEntriesOwn entries ∗
   (bv_unsigned sp + 256) ↦ₘ transactionRowWord bytes index 208 ∗
   (bv_unsigned sp + 264) ↦ₘ Z_to_bv 64 (Z.of_nat (length entries)) ∗
   (bv_unsigned sp + 272) ↦ₘ storedIndex ∗
   (bv_unsigned sp + 1744) ↦ₘ? 40 ∗ writeSuccessStorageKeysScratch sp ∗
   (bv_unsigned sp - 48) ↦ₘ? 16 ∗
   (bv_unsigned sp + 1640) ↦ₘ transactionRecipientSourceWord bytes index 265 ∗
   (bv_unsigned sp + 1648) ↦ₘ transactionRecipientSourceWord bytes index 273 ∗
   (bv_unsigned sp + 1656) ↦ₘ transactionRecipientSourceLast bytes index ∗
   (bv_unsigned sp + 120) ↦ₘ transactionRowByte bytes index 285 ∗
   (bv_unsigned sp + 128) ↦ₘ transactionRowWord bytes index 64 ∗
   bv_unsigned (transactionRowWord bytes index 192) ↦ₘ∗ dataBytes ∗
   bv_unsigned (sp + BV 64 1664)%bv ↦ₘ∗ chainBytes ∗
   transactionFieldSourceFeeRest sp base bytes processed index dataBytes accessBytes Q ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSourceBlobFeeRetained) := I.
