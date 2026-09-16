Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.ArrayByteViews.
Require Import ZesuSsz.Automation.ArrayWordViews.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsNestedSourceEntry WriteSuccessExactTransactionsNestedSuffix
  WriteSuccessExactTransactionsPrepare WriteSuccessExactTransactionsWideSignatureSuffixEntry
  WriteSuccessExactTransactionsValueMiddleWordsEntry WriteSuccessExactTransactionsRecipientTagShiftEntry
  WriteSuccessExactTransactionsSignatureFieldEntry WriteSuccessExactTransactionsGasSignatureEntry
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsFlagLoads.
Local Open Scope Z_scope.

Definition transactionPrepareCaller `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 176) ↦ₘ? 8 ∗ (bv_unsigned sp + 1648) ↦ₘ? 12 ∗
   (bv_unsigned sp + 1744) ↦ₘ? 1 ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionPrepareCaller) := I.

Definition transactionPrepareRegisters `{!islaG Sigma} `{!threadG}
    (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  ("x16" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 269)%nat)); (default (BV 8 0) (bytes !! (index + 270)%nat)); (default (BV 8 0) (bytes !! (index + 271)%nat)); (default (BV 8 0) (bytes !! (index + 272)%nat))] * 4294967296)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 267)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 268)%nat)) * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 269)%nat)) + bv_unsigned (default (BV 8 0) (bytes !! (index + 270)%nat)) * 256)) ∗
   "x5" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 271)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 272)%nat)) * 16777216)) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 275)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 276)%nat)) * 16777216)) ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 277)%nat)) + bv_unsigned (default (BV 8 0) (bytes !! (index + 278)%nat)) * 256)) ∗
   "x29" ↦ᵣ RVal_Bits (transactionRowWord bytes index 64) ∗
   "x30" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 271)%nat)) * 65536)) ∗
   "x27" ↦ᵣ RVal_Bits (transactionRowByte bytes index 32) ∗
   "x18" ↦ᵣ RVal_Bits (transactionRowWord bytes index 48) ∗
   "x20" ↦ᵣ RVal_Bits (transactionRowWord bytes index 56) ∗
   "x31" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 278)%nat)) * 256)) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionPrepareRegisters) := I.

Definition transactionPrepareRetained `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  ("x19" ↦ᵣ RVal_Bits (transactionRowWord bytes index 224) ∗
   "x12" ↦ᵣ RVal_Bits (transactionRowWord bytes index 248) ∗
   "x22" ↦ᵣ RVal_Bits (transactionRowWord bytes index 200) ∗
   (bv_unsigned sp + 136) ↦ₘ (transactionRowWord bytes index 232) ∗
   (bv_unsigned sp + 160) ↦ₘ (transactionRowWord bytes index 248) ∗
   (bv_unsigned sp + 168) ↦ₘ (transactionRowWord bytes index 240) ∗
   (bv_unsigned sp + 256) ↦ₘ (transactionRowWord bytes index 208) ∗
   (bv_unsigned sp + 264) ↦ₘ (transactionRowWord bytes index 216) ∗
   (bv_unsigned sp + 1640) ↦ₘ (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 265)%nat)); (default (BV 8 0) (bytes !! (index + 266)%nat)); (default (BV 8 0) (bytes !! (index + 267)%nat)); (default (BV 8 0) (bytes !! (index + 268)%nat)); (default (BV 8 0) (bytes !! (index + 269)%nat)); (default (BV 8 0) (bytes !! (index + 270)%nat)); (default (BV 8 0) (bytes !! (index + 271)%nat)); (default (BV 8 0) (bytes !! (index + 272)%nat))])) ∗
   transactionPrepareRegisters bytes index
     (transactionStoredSignatureTail sp row chain chainTag bytes index P) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionPrepareRetained) := I.

Lemma transactions_nested_suffix_prepare_entry `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) :
  transactionNestedSuffixPost sp row base bytes index
    (transactionNestedSuffixRetained sp row chain chainTag bytes index (transactionPrepareCaller sp P)) -∗
  transactionPrepareEntry sp row (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 273)%nat)); (default (BV 8 0) (bytes !! (index + 274)%nat)); (default (BV 8 0) (bytes !! (index + 275)%nat)); (default (BV 8 0) (bytes !! (index + 276)%nat)); (default (BV 8 0) (bytes !! (index + 277)%nat)); (default (BV 8 0) (bytes !! (index + 278)%nat)); (default (BV 8 0) (bytes !! (index + 279)%nat)); (default (BV 8 0) (bytes !! (index + 280)%nat))]))
    (Z_to_bv 32 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 281)%nat)); (default (BV 8 0) (bytes !! (index + 282)%nat)); (default (BV 8 0) (bytes !! (index + 283)%nat)); (default (BV 8 0) (bytes !! (index + 284)%nat))])) (default (BV 8 0) (bytes !! (index + 264)%nat))
    base bytes index (transactionPrepareRetained sp row chain chainTag bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionNestedSuffixPost /transactionNestedSuffixRetained /transactionNestedRecipientContext
    /transactionNestedRegistersNo19 /transactionStoredSignatureTail /transactionSignatureStackFrame
    /transactionRecipientAssemblyStackContents /transactionRecipientAssemblyFields
    /transactionSignatureFieldRetained /transactionGasSignatureRetained /transactionPrepareCaller
    array_byte_four_register_width /transactionRowByte !array_byte_default) in "Hpost".
  zesu_open_resource_groups.
  rewrite /transactionPrepareEntry /transactionPrepareRetained /transactionPrepareRegisters
    /transactionStoredSignatureTail /transactionSignatureStackFrame /transactionRecipientAssemblyStackContents
    /transactionRecipientAssemblyFields /transactionSignatureFieldRetained /transactionGasSignatureRetained
    /transactionRowByte !array_byte_default.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_nested_suffix_prepare_entry.
