Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayByteViews.
Require Import ZesuSsz.Automation.RegPacking.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsRecipientHighPairsEntry
  WriteSuccessExactTransactionsRecipientPairs WriteSuccessExactTransactionsRecipientMiddle
  WriteSuccessExactTransactionsRecipientTagShiftEntry WriteSuccessExactTransactionsFlagLoads.
Local Open Scope Z_scope.

Definition transactionRecipientAssemblyResident `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗
   (bv_unsigned sp + 120) ↦ₘ (transactionRowByte bytes index 285) ∗
   ⌜(bv_unsigned sp `mod` 8 = 0)%Z⌝ ∗ ⌜((mapRamBase defaultMap) <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 128 < (machineRamEnd defaultMap))%Z⌝ ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 281)%nat)); (default (BV 8 0) (bytes !! (index + 282)%nat))])) ∗
   "x19" ↦ᵣ RVal_Bits (transactionRowByte bytes index 266) ∗
   "x20" ↦ᵣ RVal_Bits (transactionRowByte bytes index 267) ∗
   "x11" ↦ᵣ RVal_Bits (transactionRowByte bytes index 264) ∗
   "x12" ↦ᵣ RVal_Bits (transactionRowByte bytes index 265) ∗
   (bv_unsigned sp + 1664) ↦ₘ chain ∗ (bv_unsigned sp + 1672) ↦ₘ chainTag ∗
   "x13" ↦ᵣ RVal_Bits (transactionRowByte bytes index 280) ∗
   ⌜(bv_unsigned row `mod` 8 = 0)%Z⌝ ∗
   transactionRecipientPairRemainder bytes index (transactionRecipientAssemblyFields sp row bytes index P) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientAssemblyResident) := I.

Definition transactionRecipientMiddleRetained `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x15" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 283)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 284)%nat)) * 16777216)) ∗
   "x16" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 273)%nat)) + bv_unsigned (default (BV 8 0) (bytes !! (index + 274)%nat)) * 256)) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 275)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 276)%nat)) * 16777216)) ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 277)%nat)) + bv_unsigned (default (BV 8 0) (bytes !! (index + 278)%nat)) * 256)) ∗
   "x31" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 278)%nat)) * 256)) ∗
   transactionRecipientAssemblyResident sp row chain chainTag bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientMiddleRetained) := I.

Lemma transactions_recipient_pairs_middle_entry `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base bytes index (P : iProp Sigma) :
  transactionRecipientPairsPost
    (default (BV 8 0) (bytes !! (index + 283)%nat))
    (default (BV 8 0) (bytes !! (index + 284)%nat))
    (default (BV 8 0) (bytes !! (index + 273)%nat))
    (default (BV 8 0) (bytes !! (index + 274)%nat))
    (default (BV 8 0) (bytes !! (index + 275)%nat))
    (default (BV 8 0) (bytes !! (index + 276)%nat))
    (default (BV 8 0) (bytes !! (index + 277)%nat))
    (default (BV 8 0) (bytes !! (index + 278)%nat))
    (transactionRecipientAssemblyContextNo15 sp row chain chainTag base bytes index
      (transactionRecipientPairRemainder bytes index (transactionRecipientAssemblyFields sp row bytes index P))) -∗
  transactionRecipientMiddleEntry row base bytes index
    (transactionRecipientMiddleRetained sp row chain chainTag bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionRecipientPairsPost /transactionRecipientAssemblyContextNo15) in "Hpost".
  iDestruct "Hpost" as "(Hsys & H15 & H16 & H17 & H6 & H7 & H29 & H28 & H31 & H30 & Hcontext & _)".
  iPoseProof (reg_col_bv_list_shape
    [("x7", Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 274)%nat)) * 256));
     ("x28", Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 275)%nat)) * 65536));
     ("x29", Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 276)%nat)) * 16777216));
     ("x30", bv_zero_extend 64 (default (BV 8 0) (bytes !! (index + 277)%nat)))]
    with "[H7 H28 H29 H30]") as "Hregs".
  { cbn. iFrame. }
  zesu_open_resource_groups.
  rewrite /transactionRecipientMiddleEntry /transactionRecipientMiddleRetained
    /transactionRecipientAssemblyResident.
  iFrame. repeat iSplit; try done. iPureIntro. lia.
Qed.
Print Assumptions transactions_recipient_pairs_middle_entry.

