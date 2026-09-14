Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessStorageKeysSpec WriteSuccessAccessListsSpec
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsFlagLoads
  WriteSuccessExactTransactionsSourceFieldLayout WriteSuccessExactTransactionsSourceBlobFeeFrame.

Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.IslarisMachine.

Definition transactionSourceAuthorizationLoanRemainder `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (bytes : list (bv 8)) (processed index : nat)
    (dataBytes accessBytes chainBytes : list (bv 8)) (entries : list writeSuccessAccessEntry)
    (blobBytes : list (bv 8)) (Q : iProp Sigma) : iProp Sigma :=
  (∃ pointer storedIndex : bv 64,
   ⌜bv_unsigned sp + 1896 < machineRamEnd defaultMap⌝ ∗
   "x19" ↦ᵣ RVal_Bits pointer ∗ "x22" ↦ᵣ RVal_Bits (BV 64 0) ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
     ["x3"; "x4"; "x6"; "x7"; "x16"; "x17"; "x20"; "x21";
      "x23"; "x24"; "x25"; "x26"; "x27"; "x28"; "x29"; "x30"; "x31"]) ∗
   writeSuccessByteArrayOwn (transactionRowWord bytes index 224) blobBytes ∗
   (bv_unsigned sp + 136) ↦ₘ transactionRowWord bytes index 232 ∗
   bv_unsigned (transactionRowWord bytes index 208) ↦ₘ∗ accessBytes ∗
   writeSuccessAccessEntriesOwn entries ∗
   (bv_unsigned sp + 256) ↦ₘ transactionRowWord bytes index 208 ∗
   (bv_unsigned sp + 264) ↦ₘ Z_to_bv 64 (Z.of_nat (length entries)) ∗
   (bv_unsigned sp + 272) ↦ₘ storedIndex ∗
   writeSuccessStorageKeysScratch sp ∗ (bv_unsigned sp + 1888) ↦ₘ? 8 ∗
   (bv_unsigned sp + 1640) ↦ₘ transactionRecipientSourceWord bytes index 265 ∗
   (bv_unsigned sp + 1648) ↦ₘ transactionRecipientSourceWord bytes index 273 ∗
   (bv_unsigned sp + 1656) ↦ₘ transactionRecipientSourceLast bytes index ∗
   (bv_unsigned sp + 120) ↦ₘ transactionRowByte bytes index 285 ∗
   (bv_unsigned sp + 128) ↦ₘ transactionRowWord bytes index 64 ∗
   bv_unsigned (transactionRowWord bytes index 192) ↦ₘ∗ dataBytes ∗
   bv_unsigned (sp + BV 64 1664)%bv ↦ₘ∗ chainBytes ∗
   base ↦ₘ∗ bytes ∗ (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 248) ↦ₘ Z_to_bv 64 (Z.of_nat processed) ∗
   (bv_unsigned sp + 176) ↦ₘ transactionRowWord bytes index 256 ∗
   (bv_unsigned sp + 184) ↦ₘ transactionRowWord bytes index 120 ∗
   (bv_unsigned sp + 192) ↦ₘ transactionRowWord bytes index 112 ∗
   (bv_unsigned sp + 200) ↦ₘ transactionRowWord bytes index 104 ∗
   (bv_unsigned sp + 208) ↦ₘ transactionRowWord bytes index 128 ∗
   (bv_unsigned sp + 216) ↦ₘ transactionRowWord bytes index 96 ∗
   (bv_unsigned sp + 224) ↦ₘ transactionRowWord bytes index 152 ∗
   (bv_unsigned sp + 232) ↦ₘ transactionRowWord bytes index 144 ∗
   (bv_unsigned sp + 240) ↦ₘ transactionRowWord bytes index 136 ∗
   (bv_unsigned sp + 1660) ↦ₘ? 4 ∗ (bv_unsigned sp + 1680) ↦ₘ? 32 ∗
   ⌜dataBytes <> [] -> mapRamBase defaultMap <= bv_unsigned (transactionRowWord bytes index 192) /\
     bv_unsigned (transactionRowWord bytes index 192) + Z.of_nat (length dataBytes) < machineRamEnd defaultMap⌝ ∗
   ⌜accessBytes <> [] -> mapRamBase defaultMap <= bv_unsigned (transactionRowWord bytes index 208) /\
     bv_unsigned (transactionRowWord bytes index 208) + Z.of_nat (length accessBytes) < machineRamEnd defaultMap⌝ ∗
   Q ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSourceAuthorizationLoanRemainder) := I.

Print Assumptions transactionSourceAuthorizationLoanRemainder.
