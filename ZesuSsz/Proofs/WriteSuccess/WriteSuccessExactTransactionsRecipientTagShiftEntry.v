Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayByteViews.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsRecipientPairTagEntry WriteSuccessExactTransactionsToTag
  WriteSuccessExactTransactionsFirstRecipientEntry WriteSuccessExactTransactionsRecipientShifts
  WriteSuccessExactTransactionsOptionSourcesRegion WriteSuccessExactTransactionsSignatureFieldEntry
  WriteSuccessExactTransactionsGasSignatureEntry WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactTransactionsFlagLoads.
Local Open Scope Z_scope.

Definition transactionRecipientAssemblyFields `{!islaG Sigma} `{!threadG}
    (sp row : bv 64) bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x26" ↦ᵣ RVal_Bits (transactionRowWord bytes index 184) ∗
   "x8" ↦ᵣ RVal_Bits (transactionRowWord bytes index 192) ∗
   (bv_unsigned sp + 272) ↦ₘ (transactionRowWord bytes index 176) ∗
   transactionSignatureFieldRetained sp row bytes index
     (transactionGasSignatureRetained sp bytes index P) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientAssemblyFields) := I.

Definition transactionRecipientAssemblyContext `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) (base : Z) bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x15" ↦ᵣ RVal_Bits (transactionRowByte bytes index 285) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 120) ↦ₘ (transactionRowByte bytes index 285) ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 288 <= length bytes)%nat⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗ ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗
   ⌜(bv_unsigned sp `mod` 8 = 0)%Z⌝ ∗ ⌜((mapRamBase defaultMap) <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 128 < (machineRamEnd defaultMap))%Z⌝ ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8
     [default (BV 8 0) (bytes !! (index + 281)%nat);
      default (BV 8 0) (bytes !! (index + 282)%nat)])) ∗
   "x19" ↦ᵣ RVal_Bits (transactionRowByte bytes index 266) ∗
   "x20" ↦ᵣ RVal_Bits (transactionRowByte bytes index 267) ∗
   "x11" ↦ᵣ RVal_Bits (transactionRowByte bytes index 264) ∗
   "x12" ↦ᵣ RVal_Bits (transactionRowByte bytes index 265) ∗
   (bv_unsigned sp + 1664) ↦ₘ chain ∗ (bv_unsigned sp + 1672) ↦ₘ chainTag ∗
   "x13" ↦ᵣ RVal_Bits (transactionRowByte bytes index 280) ∗
   ⌜(bv_unsigned row `mod` 8 = 0)%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientAssemblyContext) := I.

Definition transactionRecipientAssemblyLower `{!islaG Sigma} `{!threadG}
    bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x5" ↦ᵣ RVal_Bits (transactionRowByte bytes index 272) ∗
   "x6" ↦ᵣ RVal_Bits (transactionRowByte bytes index 273) ∗
   "x29" ↦ᵣ RVal_Bits (transactionRowByte bytes index 276) ∗
   "x30" ↦ᵣ RVal_Bits (transactionRowByte bytes index 277) ∗
   "x31" ↦ᵣ RVal_Bits (transactionRowByte bytes index 278) ∗
   "x18" ↦ᵣ RVal_Bits (transactionRowByte bytes index 279) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientAssemblyLower) := I.

Lemma transactions_recipient_tag_shift_entry `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base bytes index (P : iProp Sigma) :
  transactionToTagPost sp row base bytes index (transactionToTagSourceFrame sp row chain chainTag bytes index P) -∗
  transactionRecipientShiftEntry
    (default (BV 8 0) (bytes !! (index + 283)%nat))
    (default (BV 8 0) (bytes !! (index + 284)%nat))
    (default (BV 8 0) (bytes !! (index + 274)%nat))
    (default (BV 8 0) (bytes !! (index + 275)%nat))
    (transactionRecipientAssemblyContext sp row chain chainTag base bytes index
      (transactionRecipientAssemblyLower bytes index
        (transactionRecipientAssemblyFields sp row bytes index P))).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionToTagPost /transactionToTagSourceFrame /transactionFirstRecipientTail
    /transactionOptionPrefixRetained /transactionSignatureFieldRetained /transactionGasSignatureRetained
    /transactionRowByte !array_byte_default) in "Hpost".
  zesu_open_resource_groups.
  rewrite /transactionRecipientShiftEntry /transactionRecipientAssemblyContext
    /transactionRecipientAssemblyLower /transactionRecipientAssemblyFields
    /transactionSignatureFieldRetained /transactionGasSignatureRetained /transactionRowByte !array_byte_default.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_recipient_tag_shift_entry.

