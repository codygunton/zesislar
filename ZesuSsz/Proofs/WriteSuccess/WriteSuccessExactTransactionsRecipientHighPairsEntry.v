Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayByteViews.
Require Import ZesuSsz.Automation.RegPacking.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsRecipientTagShiftEntry WriteSuccessExactTransactionsRecipientShiftsHighEntry
  WriteSuccessExactTransactionsRecipientHighShifts WriteSuccessExactTransactionsRecipientPairs
  WriteSuccessExactTransactionsFlagLoads.
Local Open Scope Z_scope.

Definition transactionRecipientAssemblyContextNo15 `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) (base : Z) bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
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
Global Instance : LithiumUnfold (@transactionRecipientAssemblyContextNo15) := I.


Definition transactionRecipientPairRemainder `{!islaG Sigma} `{!threadG}
    bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x5" ↦ᵣ RVal_Bits (transactionRowByte bytes index 272) ∗
   "x18" ↦ᵣ RVal_Bits (transactionRowByte bytes index 279) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientPairRemainder) := I.

Lemma transactions_recipient_high_pairs_entry `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base bytes index (P : iProp Sigma) :
  transactionRecipientHighShiftPost
    (default (BV 8 0) (bytes !! (index + 276)%nat))
    (default (BV 8 0) (bytes !! (index + 278)%nat))
    (transactionRecipientHighShiftFrame sp row chain chainTag base bytes index P) -∗
  transactionRecipientPairsEntry
    (default (BV 8 0) (bytes !! (index + 283)%nat))
    (default (BV 8 0) (bytes !! (index + 284)%nat))
    (default (BV 8 0) (bytes !! (index + 273)%nat))
    (default (BV 8 0) (bytes !! (index + 274)%nat))
    (default (BV 8 0) (bytes !! (index + 275)%nat))
    (default (BV 8 0) (bytes !! (index + 276)%nat))
    (default (BV 8 0) (bytes !! (index + 277)%nat))
    (default (BV 8 0) (bytes !! (index + 278)%nat))
    (transactionRecipientAssemblyContextNo15 sp row chain chainTag base bytes index
      (transactionRecipientPairRemainder bytes index (transactionRecipientAssemblyFields sp row bytes index P))).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionRecipientHighShiftPost /transactionRecipientHighShiftFrame
    /transactionRecipientAssemblyContext /transactionRecipientAssemblySmallLower
    /transactionRowByte !array_byte_default) in "Hpost".
  iDestruct "Hpost" as "(Hsys & H29 & H31 & Hframe & _)".
  iDestruct "Hframe" as "(H16 & H17 & H7 & H28 & (H15 & Hcontext) & _)".
  iPoseProof (reg_col_bv_list_shape
    [("x15", bv_zero_extend 64 (default (BV 8 0) (bytes !! (index + 285)%nat)))]
    with "[H15]") as "Hregs".
  { cbn. iFrame. }
  zesu_open_resource_groups.
  rewrite /transactionRecipientPairsEntry /transactionRecipientAssemblyContextNo15
    /transactionRecipientPairRemainder /transactionRowByte !array_byte_default.
  iFrame. repeat iSplit; done.
Qed.
Print Assumptions transactions_recipient_high_pairs_entry.

