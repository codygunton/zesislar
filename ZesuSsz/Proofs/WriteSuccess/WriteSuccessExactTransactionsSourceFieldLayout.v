Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsFlagLoads
  WriteSuccessExactTransactionsChainToNonce WriteSuccessExactTransactionsChainPriceFrame
  WriteSuccessExactTransactionsDataAccessEntry WriteSuccessTransactionsSpec
  WriteSuccessAccessListsSpec.

Definition transactionRecipientSourceWord (bytes : list (bv 8)) (index offset : nat) : bv 64 :=
  Z_to_bv 64 (little_endian_to_bv 8
    ((fun i => default (BV 8 0) (bytes !! (index + (offset + i))%nat)) <$> seq 0 8)).
Definition transactionRecipientSourceLast (bytes : list (bv 8)) (index : nat) : bv 32 :=
  Z_to_bv 32 (little_endian_to_bv 8
    ((fun i => default (BV 8 0) (bytes !! (index + (281 + i))%nat)) <$> seq 0 4)).
Definition transactionRecipientSourceOld6 (bytes : list (bv 8)) (index : nat) : bv 64 :=
  Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 277)%nat)) +
    bv_unsigned (default (BV 8 0) (bytes !! (index + 278)%nat)) * 256).

Definition transactionFieldSourceHeap `{!islaG Sigma}
    (bytes : list (bv 8)) (index : nat) (dataBytes accessBytes : list (bv 8))
    (entries : list writeSuccessAccessEntry) : iProp Sigma :=
  (writeSuccessByteArrayOwn (transactionRowWord bytes index 192) dataBytes ∗
   writeSuccessByteArrayOwn (transactionRowWord bytes index 208) accessBytes ∗
   writeSuccessAccessEntriesOwn entries ∗
   ⌜bv_unsigned (transactionRowWord bytes index 200) = length dataBytes⌝ ∗
   ⌜transactionRowWord bytes index 216 = Z_to_bv 64 (Z.of_nat (length entries))⌝ ∗
   ⌜accessBytes = writeSuccessAccessEntriesBytes entries⌝ ∗
   ⌜length accessBytes = (40 * length entries)%nat⌝ ∗
   ⌜(length entries < 2 ^ 64)%nat⌝ ∗ True)%I.
Global Instance : LithiumUnfold (@transactionFieldSourceHeap) := I.

Definition transactionFieldSourceRetained `{!islaG Sigma}
    (sp : bv 64) (base : Z) (bytes : list (bv 8)) (processed index : nat)
    (dataBytes accessBytes : list (bv 8)) (Q : iProp Sigma) : iProp Sigma :=
  (base ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 248) ↦ₘ Z_to_bv 64 (Z.of_nat processed) ∗
   (bv_unsigned sp + 144) ↦ₘ transactionRowWord bytes index 88 ∗
   (bv_unsigned sp + 152) ↦ₘ transactionRowWord bytes index 80 ∗
   (bv_unsigned sp + 160) ↦ₘ transactionRowWord bytes index 248 ∗
   (bv_unsigned sp + 168) ↦ₘ transactionRowWord bytes index 240 ∗
   (bv_unsigned sp + 176) ↦ₘ transactionRowWord bytes index 256 ∗
   (bv_unsigned sp + 184) ↦ₘ transactionRowWord bytes index 120 ∗
   (bv_unsigned sp + 192) ↦ₘ transactionRowWord bytes index 112 ∗
   (bv_unsigned sp + 200) ↦ₘ transactionRowWord bytes index 104 ∗
   (bv_unsigned sp + 208) ↦ₘ transactionRowWord bytes index 128 ∗
   (bv_unsigned sp + 216) ↦ₘ transactionRowWord bytes index 96 ∗
   (bv_unsigned sp + 224) ↦ₘ transactionRowWord bytes index 152 ∗
   (bv_unsigned sp + 232) ↦ₘ transactionRowWord bytes index 144 ∗
   (bv_unsigned sp + 240) ↦ₘ transactionRowWord bytes index 136 ∗
   (bv_unsigned sp + 1660) ↦ₘ? 4 ∗
   (bv_unsigned sp + 1680) ↦ₘ? 32 ∗ (bv_unsigned sp + 1784) ↦ₘ? 112 ∗
   ⌜dataBytes <> [] -> (mapRamBase defaultMap) <= bv_unsigned (transactionRowWord bytes index 192) /\
     bv_unsigned (transactionRowWord bytes index 192) + Z.of_nat (length dataBytes) < (machineRamEnd defaultMap)⌝ ∗
   ⌜accessBytes <> [] -> (mapRamBase defaultMap) <= bv_unsigned (transactionRowWord bytes index 208) /\
     bv_unsigned (transactionRowWord bytes index 208) + Z.of_nat (length accessBytes) < (machineRamEnd defaultMap)⌝ ∗
   Q ∗ True)%I.
Global Instance : LithiumUnfold (@transactionFieldSourceRetained) := I.

Definition transactionSourceFieldCore `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (bytes : list (bv 8)) (processed index : nat)
    (dataBytes accessBytes : list (bv 8)) (entries : list writeSuccessAccessEntry)
    (Q : iProp Sigma) : iProp Sigma :=
  transactionChainPriceRecipientCaller sp
      (transactionRowWord bytes index 0) (transactionRowWord bytes index 8)
      (transactionRowByte bytes index 32)
      (transactionRowWord bytes index 16) (transactionRowWord bytes index 24)
      (transactionRowWord bytes index 184) (transactionRowByte bytes index 285)
      (transactionRecipientSourceWord bytes index 265)
      (transactionRecipientSourceWord bytes index 273)
      (transactionRowWord bytes index 48) (transactionRowWord bytes index 56)
      (transactionRowWord bytes index 64) (transactionRowWord bytes index 72)
      (transactionRowWord bytes index 248) (transactionRecipientSourceWord bytes index 273)
      (transactionRowWord bytes index 192) (transactionRowWord bytes index 200)
      (transactionRowWord bytes index 216) (transactionRecipientSourceLast bytes index)
      dataBytes (transactionAccessAfterDataCaller sp
        (transactionRowWord bytes index 224) (transactionRowWord bytes index 232)
        (transactionRowWord bytes index 216) (bv_unsigned (transactionRowWord bytes index 208))
        entries accessBytes (transactionFieldSourceRetained sp base bytes processed index dataBytes accessBytes Q)).
Global Instance : LithiumUnfold (@transactionSourceFieldCore) := I.

Definition transactionSourceFieldCaller `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (bytes : list (bv 8)) (processed index : nat)
    (dataBytes accessBytes : list (bv 8)) (entries : list writeSuccessAccessEntry)
    (Q : iProp Sigma) : iProp Sigma :=
  transactionChainNonceCaller sp (transactionRowWord bytes index 176)
    (transactionSourceFieldCore sp base bytes processed index dataBytes accessBytes entries Q).
Global Instance : LithiumUnfold (@transactionSourceFieldCaller) := I.

Definition transactionSourceFieldNoneCaller `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (bytes : list (bv 8)) (processed index : nat)
    (dataBytes accessBytes : list (bv 8)) (entries : list writeSuccessAccessEntry)
    (Q : iProp Sigma) : iProp Sigma :=
  transactionChainNonceCaller sp (transactionRowWord bytes index 176)
    ("x8" ↦ᵣ RVal_Bits (transactionRowWord bytes index 192) ∗
      transactionSourceFieldCore sp base bytes processed index dataBytes accessBytes entries Q ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSourceFieldNoneCaller) := I.
