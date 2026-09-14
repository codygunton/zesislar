Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.RegPacking.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsRecipientWordsSignatureValuesEntry WriteSuccessExactTransactionsSignatureValues
  WriteSuccessExactTransactionsValueMiddleWordsEntry WriteSuccessExactTransactionsRecipientLowWords
  WriteSuccessExactTransactionsRecipientWide WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactTransactionsFlagLoads.
Local Open Scope Z_scope.

Definition transactionSignatureAssemblyStorage `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) (base : Z) bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   "x21" ↦ᵣ RVal_Bits (transactionRowWord bytes index 72) ∗
   (bv_unsigned sp + 128) ↦ₘ (transactionRowWord bytes index 64) ∗
   (bv_unsigned sp + 144) ↦ₘ (transactionRowWord bytes index 88) ∗
   (bv_unsigned sp + 152) ↦ₘ (transactionRowWord bytes index 80) ∗
   (bv_unsigned sp + 216) ↦ₘ (transactionRowWord bytes index 96) ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 104 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= base⌝ ∗ ⌜base + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗ ⌜bv_unsigned sp + 224 < (machineRamEnd defaultMap)⌝ ∗
   transactionRecipientAssemblyStackContents sp row chain chainTag bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureAssemblyStorage) := I.

Definition transactionRecipientWideRegisters `{!islaG Sigma} `{!threadG}
    bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 281)%nat)); (default (BV 8 0) (bytes !! (index + 282)%nat)); (default (BV 8 0) (bytes !! (index + 283)%nat)); (default (BV 8 0) (bytes !! (index + 284)%nat))])) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 275)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 276)%nat)) * 16777216)) ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 277)%nat)) + bv_unsigned (default (BV 8 0) (bytes !! (index + 278)%nat)) * 256)) ∗
   "x29" ↦ᵣ RVal_Bits (transactionRowWord bytes index 64) ∗
   "x30" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 271)%nat)) * 65536)) ∗
   "x27" ↦ᵣ RVal_Bits (transactionRowByte bytes index 32) ∗
   "x18" ↦ᵣ RVal_Bits (transactionRowWord bytes index 48) ∗
   "x20" ↦ᵣ RVal_Bits (transactionRowWord bytes index 56) ∗
   "x19" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 266)%nat)) * 256)) ∗
   "x31" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 278)%nat)) * 256)) ∗
   "x11" ↦ᵣ RVal_Bits (transactionRowByte bytes index 264) ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientWideRegisters) := I.

Definition transactionRecipientLowWordsFrame `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) (base : Z) bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x15" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 273)%nat)); (default (BV 8 0) (bytes !! (index + 274)%nat)); (default (BV 8 0) (bytes !! (index + 275)%nat)); (default (BV 8 0) (bytes !! (index + 276)%nat))])) ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 277)%nat)); (default (BV 8 0) (bytes !! (index + 278)%nat)); (default (BV 8 0) (bytes !! (index + 279)%nat)); (default (BV 8 0) (bytes !! (index + 280)%nat))])) ∗
   transactionRecipientWideRegisters bytes index
     (transactionSignatureAssemblyStorage sp row chain chainTag base bytes index P) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientLowWordsFrame) := I.

Definition transactionRecipientWideFrame `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) (base : Z) bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x7" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 267)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 268)%nat)) * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 269)%nat)) + bv_unsigned (default (BV 8 0) (bytes !! (index + 270)%nat)) * 256)) ∗
   "x5" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 271)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 272)%nat)) * 16777216)) ∗
   transactionRecipientWideRegisters bytes index
     (transactionSignatureAssemblyStorage sp row chain chainTag base bytes index P) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientWideFrame) := I.

Lemma transactions_signature_values_low_words_entry `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base bytes index (P : iProp Sigma) :
  transactionSignatureValuesPost sp row base bytes index
    (transactionSignatureValuesRetained sp row chain chainTag bytes index P) -∗
  transactionRecipientLowWordsEntry
    (default (BV 8 0) (bytes !! (index + 265)%nat))
    (default (BV 8 0) (bytes !! (index + 266)%nat))
    (default (BV 8 0) (bytes !! (index + 267)%nat))
    (default (BV 8 0) (bytes !! (index + 268)%nat))
    (default (BV 8 0) (bytes !! (index + 269)%nat))
    (default (BV 8 0) (bytes !! (index + 270)%nat))
    (default (BV 8 0) (bytes !! (index + 271)%nat))
    (default (BV 8 0) (bytes !! (index + 272)%nat))
    (transactionRecipientLowWordsFrame sp row chain chainTag base bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionSignatureValuesPost /transactionSignatureValuesRetained
    /transactionRecipientMiddleFixedRegisters) in "Hpost".
  iDestruct "Hpost" as "(Hsys & Hsp & Hrow & H21 & H16 & Hframe)".
  iPoseProof (reg_col_bv_list_shape [("x16", transactionRowWord bytes index 96)]
    with "[H16]") as "Hregs".
  { cbn. iFrame. }
  zesu_open_resource_groups.
  rewrite /transactionRecipientLowWordsEntry /transactionRecipientLowWordsFrame
    /transactionRecipientWideRegisters /transactionSignatureAssemblyStorage.
  iFrame. repeat iSplit; done.
Qed.
Print Assumptions transactions_signature_values_low_words_entry.

Lemma transactions_recipient_low_words_wide_entry `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base bytes index (P : iProp Sigma) :
  transactionRecipientLowWordsPost
    (default (BV 8 0) (bytes !! (index + 265)%nat))
    (default (BV 8 0) (bytes !! (index + 266)%nat))
    (default (BV 8 0) (bytes !! (index + 267)%nat))
    (default (BV 8 0) (bytes !! (index + 268)%nat))
    (default (BV 8 0) (bytes !! (index + 269)%nat))
    (default (BV 8 0) (bytes !! (index + 270)%nat))
    (default (BV 8 0) (bytes !! (index + 271)%nat))
    (default (BV 8 0) (bytes !! (index + 272)%nat))
    (transactionRecipientLowWordsFrame sp row chain chainTag base bytes index P) -∗
  transactionRecipientWideEntry
    (default (BV 8 0) (bytes !! (index + 265)%nat))
    (default (BV 8 0) (bytes !! (index + 266)%nat))
    (default (BV 8 0) (bytes !! (index + 267)%nat))
    (default (BV 8 0) (bytes !! (index + 268)%nat))
    (default (BV 8 0) (bytes !! (index + 269)%nat))
    (default (BV 8 0) (bytes !! (index + 270)%nat))
    (default (BV 8 0) (bytes !! (index + 271)%nat))
    (default (BV 8 0) (bytes !! (index + 272)%nat))
    (default (BV 8 0) (bytes !! (index + 273)%nat))
    (default (BV 8 0) (bytes !! (index + 274)%nat))
    (default (BV 8 0) (bytes !! (index + 275)%nat))
    (default (BV 8 0) (bytes !! (index + 276)%nat))
    (default (BV 8 0) (bytes !! (index + 277)%nat))
    (default (BV 8 0) (bytes !! (index + 278)%nat))
    (default (BV 8 0) (bytes !! (index + 279)%nat))
    (default (BV 8 0) (bytes !! (index + 280)%nat))
    (transactionRecipientWideFrame sp row chain chainTag base bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionRecipientLowWordsPost /transactionRecipientLowWordsFrame) in "Hpost".
  zesu_open_resource_groups.
  rewrite /transactionRecipientWideEntry /transactionRecipientWideFrame.
  iFrame.
Qed.
Print Assumptions transactions_recipient_low_words_wide_entry.

