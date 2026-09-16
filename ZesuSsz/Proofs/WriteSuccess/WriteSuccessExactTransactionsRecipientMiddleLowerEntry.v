Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayByteViews.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsRecipientPairsMiddleEntry WriteSuccessExactTransactionsRecipientMiddle
  WriteSuccessExactTransactionsRecipientLowerShifts WriteSuccessExactTransactionsRecipientHighPairsEntry
  WriteSuccessExactTransactionsRecipientTagShiftEntry WriteSuccessExactTransactionsFlagLoads.
Local Open Scope Z_scope.

Definition transactionRecipientLowerRetained `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) (base : Z) bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x28" ↦ᵣ RVal_Bits (transactionRowByte bytes index 269) ∗
   "x30" ↦ᵣ RVal_Bits (transactionRowByte bytes index 271) ∗
   "x15" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (default (BV 8 0) (bytes !! (index + 283)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 284)%nat)) * 16777216)) ∗
   "x16" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (default (BV 8 0) (bytes !! (index + 273)%nat)) + bv_unsigned (default (BV 8 0) (bytes !! (index + 274)%nat)) * 256)) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (default (BV 8 0) (bytes !! (index + 275)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 276)%nat)) * 16777216)) ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (default (BV 8 0) (bytes !! (index + 277)%nat)) + bv_unsigned (default (BV 8 0) (bytes !! (index + 278)%nat)) * 256)) ∗
   "x31" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 278)%nat)) * 256)) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 120) ↦ₘ (transactionRowByte bytes index 285) ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 272 <= length bytes)%nat⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗ ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗
   ⌜(bv_unsigned sp `mod` 8 = 0)%Z⌝ ∗ ⌜((mapRamBase defaultMap) <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 128 < (machineRamEnd defaultMap))%Z⌝ ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 281)%nat)); (default (BV 8 0) (bytes !! (index + 282)%nat))])) ∗
   "x11" ↦ᵣ RVal_Bits (transactionRowByte bytes index 264) ∗
   "x12" ↦ᵣ RVal_Bits (transactionRowByte bytes index 265) ∗
   "x5" ↦ᵣ RVal_Bits (transactionRowByte bytes index 272) ∗
   (bv_unsigned sp + 1664) ↦ₘ chain ∗ (bv_unsigned sp + 1672) ↦ₘ chainTag ∗
   ⌜(bv_unsigned row `mod` 8 = 0)%Z⌝ ∗
   transactionRecipientAssemblyFields sp row bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientLowerRetained) := I.

Lemma transactions_recipient_middle_lower_entry `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base bytes index (P : iProp Sigma) :
  transactionRecipientMiddlePost row base bytes index
    (transactionRecipientMiddleRetained sp row chain chainTag bytes index P) -∗
  transactionRecipientLowerShiftEntry
    (default (BV 8 0) (bytes !! (index + 279)%nat))
    (default (BV 8 0) (bytes !! (index + 280)%nat))
    (default (BV 8 0) (bytes !! (index + 266)%nat))
    (default (BV 8 0) (bytes !! (index + 267)%nat))
    (default (BV 8 0) (bytes !! (index + 268)%nat))
    (default (BV 8 0) (bytes !! (index + 270)%nat))
    (transactionRecipientLowerRetained sp row chain chainTag base bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionRecipientMiddlePost /transactionRecipientMiddleRetained
    /transactionRecipientAssemblyResident /transactionRecipientPairRemainder
    /transactionRowByte !array_byte_default) in "Hpost".
  zesu_open_resource_groups.
  rewrite /transactionRecipientLowerShiftEntry /transactionRecipientLowerRetained
    /transactionRowByte !array_byte_default.
  iFrame. repeat iSplit; done.
Qed.
Print Assumptions transactions_recipient_middle_lower_entry.

