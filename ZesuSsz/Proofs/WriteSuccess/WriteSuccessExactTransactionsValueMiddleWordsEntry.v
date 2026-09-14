Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteViews.
Require Import ZesuSsz.Automation.ArrayPairViews.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsRecipientLowerPairsValueEntry WriteSuccessExactTransactionsValuePrefix
  WriteSuccessExactTransactionsRecipientLowerShiftsPairsEntry
  WriteSuccessExactTransactionsRecipientMiddlePair WriteSuccessExactTransactionsRecipientWords
  WriteSuccessExactTransactionsRecipientTagShiftEntry WriteSuccessExactTransactionsSignatureFieldEntry
  WriteSuccessExactTransactionsGasSignatureEntry WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactTransactionsFlagLoads.
Local Open Scope Z_scope.

Definition transactionRecipientMiddlePairCaller `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 128) ↦ₘ? 8 ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientMiddlePairCaller) := I.

Definition transactionRecipientMiddleFixedRegisters `{!islaG Sigma} `{!threadG}
    bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x27" ↦ᵣ RVal_Bits (transactionRowByte bytes index 32) ∗
   "x18" ↦ᵣ RVal_Bits (transactionRowWord bytes index 48) ∗
   "x20" ↦ᵣ RVal_Bits (transactionRowWord bytes index 56) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 265)%nat)) + bv_unsigned (default (BV 8 0) (bytes !! (index + 266)%nat)) * 256)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 267)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 268)%nat)) * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 269)%nat)) + bv_unsigned (default (BV 8 0) (bytes !! (index + 270)%nat)) * 256)) ∗
   "x19" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 266)%nat)) * 256)) ∗
   "x31" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 278)%nat)) * 256)) ∗
   "x11" ↦ᵣ RVal_Bits (transactionRowByte bytes index 264) ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientMiddleFixedRegisters) := I.

Definition transactionRecipientAssemblyStackContents `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) bytes index (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 120) ↦ₘ (transactionRowByte bytes index 285) ∗
   (bv_unsigned sp + 1664) ↦ₘ chain ∗ (bv_unsigned sp + 1672) ↦ₘ chainTag ∗
   transactionRecipientAssemblyFields sp row bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientAssemblyStackContents) := I.

Definition transactionRecipientMiddleStableFrame `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) (base : Z) bytes index (P : iProp Sigma) : iProp Sigma :=
  transactionRecipientMiddleFixedRegisters bytes index
    ("x10" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
     ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
     ⌜(index + 72 <= length bytes)%nat⌝ ∗
     ⌜(0x20000000 <= base)%Z⌝ ∗ ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗
     transactionRecipientAssemblyStackContents sp row chain chainTag bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientMiddleStableFrame) := I.

Definition transactionRecipientMiddlePairFrame `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) (base : Z) bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 279)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 280)%nat)) * 16777216)) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 281)%nat)); (default (BV 8 0) (bytes !! (index + 282)%nat))])) ∗
   "x15" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 283)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 284)%nat)) * 16777216)) ∗
   "x16" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 273)%nat)) + bv_unsigned (default (BV 8 0) (bytes !! (index + 274)%nat)) * 256)) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 275)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 276)%nat)) * 16777216)) ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 277)%nat)) + bv_unsigned (default (BV 8 0) (bytes !! (index + 278)%nat)) * 256)) ∗
   transactionRecipientMiddleStableFrame sp row chain chainTag base bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientMiddlePairFrame) := I.

Definition transactionRecipientWordsRetained `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) (base : Z) bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗
   "x29" ↦ᵣ RVal_Bits (transactionRowWord bytes index 64) ∗
   "x30" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 271)%nat)) * 65536)) ∗
   "x5" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 271)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 272)%nat)) * 16777216)) ∗
   (bv_unsigned sp + 128) ↦ₘ (transactionRowWord bytes index 64) ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 136 < 0x40000000⌝ ∗
   transactionRecipientMiddleStableFrame sp row chain chainTag base bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientWordsRetained) := I.

Lemma transactions_value_prefix_middle_pair_entry `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base bytes index (P : iProp Sigma) :
  transactionValuePrefixPost row base bytes index
    (transactionValuePrefixRetained sp row chain chainTag bytes index (transactionRecipientMiddlePairCaller sp P)) -∗
  transactionRecipientMiddlePairEntry sp (transactionRowWord bytes index 64) (default (BV 8 0) (bytes !! (index + 271)%nat)) (default (BV 8 0) (bytes !! (index + 272)%nat))
    (transactionRecipientMiddlePairFrame sp row chain chainTag base bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionValuePrefixPost /transactionValuePrefixRetained
    /transactionRecipientLowerPairRegisters /transactionRecipientAssemblyStackFrame
    /transactionRecipientAssemblyFields /transactionSignatureFieldRetained
    /transactionGasSignatureRetained /transactionRecipientMiddlePairCaller
    /transactionRowByte !array_byte_default) in "Hpost".
  zesu_open_resource_groups.
  rewrite /transactionRecipientMiddlePairEntry /transactionRecipientMiddlePairFrame
    /transactionRecipientMiddleStableFrame /transactionRecipientMiddleFixedRegisters
    /transactionRecipientAssemblyStackContents /transactionRecipientAssemblyFields
    /transactionSignatureFieldRetained /transactionGasSignatureRetained
    /transactionRowByte !array_byte_default.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_value_prefix_middle_pair_entry.

Lemma transactions_middle_pair_words_entry `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base bytes index (P : iProp Sigma) :
  transactionRecipientMiddlePairPost sp (transactionRowWord bytes index 64) (default (BV 8 0) (bytes !! (index + 271)%nat)) (default (BV 8 0) (bytes !! (index + 272)%nat))
    (transactionRecipientMiddlePairFrame sp row chain chainTag base bytes index P) -∗
  transactionRecipientWordsEntry
    (default (BV 8 0) (bytes !! (index + 281)%nat))
    (default (BV 8 0) (bytes !! (index + 282)%nat))
    (default (BV 8 0) (bytes !! (index + 283)%nat))
    (default (BV 8 0) (bytes !! (index + 284)%nat))
    (default (BV 8 0) (bytes !! (index + 273)%nat))
    (default (BV 8 0) (bytes !! (index + 274)%nat))
    (default (BV 8 0) (bytes !! (index + 275)%nat))
    (default (BV 8 0) (bytes !! (index + 276)%nat))
    (default (BV 8 0) (bytes !! (index + 277)%nat))
    (default (BV 8 0) (bytes !! (index + 278)%nat))
    (default (BV 8 0) (bytes !! (index + 279)%nat))
    (default (BV 8 0) (bytes !! (index + 280)%nat))
    (transactionRecipientWordsRetained sp row chain chainTag base bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionRecipientMiddlePairPost /transactionRecipientMiddlePairFrame
    array_byte_pair_encoding) in "Hpost".
  zesu_open_resource_groups.
  rewrite /transactionRecipientWordsEntry /transactionRecipientWordsRetained.
  iFrame. repeat iSplit; done.
Qed.
Print Assumptions transactions_middle_pair_words_entry.
