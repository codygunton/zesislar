Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.ArrayByteViews.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsRecipientTagShiftEntry WriteSuccessExactTransactionsRecipientShifts
  WriteSuccessExactTransactionsRecipientHighShifts WriteSuccessExactTransactionsFlagLoads.

Definition transactionRecipientAssemblySmallLower `{!islaG Sigma} `{!threadG}
    bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x5" ↦ᵣ RVal_Bits (transactionRowByte bytes index 272) ∗
   "x6" ↦ᵣ RVal_Bits (transactionRowByte bytes index 273) ∗
   "x30" ↦ᵣ RVal_Bits (transactionRowByte bytes index 277) ∗
   "x18" ↦ᵣ RVal_Bits (transactionRowByte bytes index 279) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientAssemblySmallLower) := I.

Definition transactionRecipientHighShiftFrame `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x16" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (default (BV 8 0) (bytes !! (index + 283)%nat)) * 65536)) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (default (BV 8 0) (bytes !! (index + 284)%nat)) * 16777216)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (default (BV 8 0) (bytes !! (index + 274)%nat)) * 256)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (default (BV 8 0) (bytes !! (index + 275)%nat)) * 65536)) ∗
   transactionRecipientAssemblyContext sp row chain chainTag base bytes index
     (transactionRecipientAssemblySmallLower bytes index
       (transactionRecipientAssemblyFields sp row bytes index P)) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientHighShiftFrame) := I.

Lemma transactions_recipient_shifts_high_entry `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base bytes index (P : iProp Sigma) :
  transactionRecipientShiftPost
    (default (BV 8 0) (bytes !! (index + 283)%nat))
    (default (BV 8 0) (bytes !! (index + 284)%nat))
    (default (BV 8 0) (bytes !! (index + 274)%nat))
    (default (BV 8 0) (bytes !! (index + 275)%nat))
    (transactionRecipientAssemblyContext sp row chain chainTag base bytes index
      (transactionRecipientAssemblyLower bytes index (transactionRecipientAssemblyFields sp row bytes index P))) -∗
  transactionRecipientHighShiftEntry
    (default (BV 8 0) (bytes !! (index + 276)%nat))
    (default (BV 8 0) (bytes !! (index + 278)%nat))
    (transactionRecipientHighShiftFrame sp row chain chainTag base bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionRecipientShiftPost /transactionRecipientAssemblyContext
    /transactionRecipientAssemblyLower /transactionRowByte !array_byte_default) in "Hpost".
  zesu_open_resource_groups.
  rewrite /transactionRecipientHighShiftEntry /transactionRecipientHighShiftFrame
    /transactionRecipientAssemblyContext /transactionRecipientAssemblySmallLower
    /transactionRowByte !array_byte_default.
  iFrame. repeat iSplit; done.
Qed.
Print Assumptions transactions_recipient_shifts_high_entry.

