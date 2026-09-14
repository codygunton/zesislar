Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteViews.
Require Import ZesuSsz.Automation.Resources.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsPrepareSourceEntry WriteSuccessExactTransactionsPrepare
  WriteSuccessExactTransactionsTypeOutput WriteSuccessExactTransactionsNestedSourceEntry
  WriteSuccessExactTransactionsWideSignatureSuffixEntry WriteSuccessExactTransactionsValueMiddleWordsEntry
  WriteSuccessExactTransactionsRecipientTagShiftEntry WriteSuccessExactTransactionsSignatureFieldEntry
  WriteSuccessExactTransactionsGasSignatureEntry WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactTransactionsFlagLoads.
Local Open Scope Z_scope.
Definition transactionTypeSourceCaller `{!islaG Sigma} `{!threadG}
    (sp oldra : bv 64) (kind : bv 8) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x1" ↦ᵣ RVal_Bits oldra ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 1) [kind] tail) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionTypeSourceCaller) := I.

Definition transactionTypeSourceRegisters `{!islaG Sigma} `{!threadG}
    (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  ("x16" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 269)%nat)); (default (BV 8 0) (bytes !! (index + 270)%nat)); (default (BV 8 0) (bytes !! (index + 271)%nat)); (default (BV 8 0) (bytes !! (index + 272)%nat))] * 4294967296)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 267)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 268)%nat)) * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 269)%nat)) + bv_unsigned (default (BV 8 0) (bytes !! (index + 270)%nat)) * 256)) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 275)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 276)%nat)) * 16777216)) ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 277)%nat)) + bv_unsigned (default (BV 8 0) (bytes !! (index + 278)%nat)) * 256)) ∗
   "x29" ↦ᵣ RVal_Bits (transactionRowWord bytes index 64) ∗
   "x30" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 271)%nat)) * 65536)) ∗
   "x27" ↦ᵣ RVal_Bits (transactionRowByte bytes index 32) ∗
   "x18" ↦ᵣ RVal_Bits (transactionRowWord bytes index 48) ∗
   "x20" ↦ᵣ RVal_Bits (transactionRowWord bytes index 56) ∗
   "x31" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 278)%nat)) * 256)) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionTypeSourceRegisters) := I.

Definition transactionTypeSourceRetained `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (base ↦ₘ∗ bytes ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 273)%nat)); (default (BV 8 0) (bytes !! (index + 274)%nat)); (default (BV 8 0) (bytes !! (index + 275)%nat)); (default (BV 8 0) (bytes !! (index + 276)%nat)); (default (BV 8 0) (bytes !! (index + 277)%nat)); (default (BV 8 0) (bytes !! (index + 278)%nat)); (default (BV 8 0) (bytes !! (index + 279)%nat)); (default (BV 8 0) (bytes !! (index + 280)%nat))])) ∗
   "x14" ↦ᵣ RVal_Bits (bv_zero_extend 64 (Z_to_bv 32 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 281)%nat)); (default (BV 8 0) (bytes !! (index + 282)%nat)); (default (BV 8 0) (bytes !! (index + 283)%nat)); (default (BV 8 0) (bytes !! (index + 284)%nat))]))) ∗
   (bv_unsigned sp + 176) ↦ₘ (transactionRowWord bytes index 256) ∗
   (bv_unsigned sp + 1648) ↦ₘ (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 273)%nat)); (default (BV 8 0) (bytes !! (index + 274)%nat)); (default (BV 8 0) (bytes !! (index + 275)%nat)); (default (BV 8 0) (bytes !! (index + 276)%nat)); (default (BV 8 0) (bytes !! (index + 277)%nat)); (default (BV 8 0) (bytes !! (index + 278)%nat)); (default (BV 8 0) (bytes !! (index + 279)%nat)); (default (BV 8 0) (bytes !! (index + 280)%nat))])) ∗
   (bv_unsigned sp + 1656) ↦ₘ (Z_to_bv 32 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 281)%nat)); (default (BV 8 0) (bytes !! (index + 282)%nat)); (default (BV 8 0) (bytes !! (index + 283)%nat)); (default (BV 8 0) (bytes !! (index + 284)%nat))])) ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 264 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= base⌝ ∗ ⌜base + Z.of_nat (length bytes) < 0x40000000⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp⌝ ∗ ⌜bv_unsigned sp + 1745 < 0x40000000⌝ ∗
   "x19" ↦ᵣ RVal_Bits (transactionRowWord bytes index 224) ∗
   "x12" ↦ᵣ RVal_Bits (transactionRowWord bytes index 248) ∗
   "x22" ↦ᵣ RVal_Bits (transactionRowWord bytes index 200) ∗
   (bv_unsigned sp + 136) ↦ₘ (transactionRowWord bytes index 232) ∗
   (bv_unsigned sp + 160) ↦ₘ (transactionRowWord bytes index 248) ∗
   (bv_unsigned sp + 168) ↦ₘ (transactionRowWord bytes index 240) ∗
   (bv_unsigned sp + 256) ↦ₘ (transactionRowWord bytes index 208) ∗
   (bv_unsigned sp + 264) ↦ₘ (transactionRowWord bytes index 216) ∗
   (bv_unsigned sp + 1640) ↦ₘ (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 265)%nat)); (default (BV 8 0) (bytes !! (index + 266)%nat)); (default (BV 8 0) (bytes !! (index + 267)%nat)); (default (BV 8 0) (bytes !! (index + 268)%nat)); (default (BV 8 0) (bytes !! (index + 269)%nat)); (default (BV 8 0) (bytes !! (index + 270)%nat)); (default (BV 8 0) (bytes !! (index + 271)%nat)); (default (BV 8 0) (bytes !! (index + 272)%nat))])) ∗
   transactionTypeSourceRegisters bytes index
     (transactionStoredSignatureTail sp row chain chainTag bytes index P) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionTypeSourceRetained) := I.

Lemma transactions_prepare_type_source_entry `{!islaG Sigma} `{!threadG}
    sp row chain chainTag oldra base (bytes : list (bv 8)) (index : nat) tail (P : iProp Sigma) :
  transactionPreparePost sp row (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 273)%nat)); (default (BV 8 0) (bytes !! (index + 274)%nat)); (default (BV 8 0) (bytes !! (index + 275)%nat)); (default (BV 8 0) (bytes !! (index + 276)%nat)); (default (BV 8 0) (bytes !! (index + 277)%nat)); (default (BV 8 0) (bytes !! (index + 278)%nat)); (default (BV 8 0) (bytes !! (index + 279)%nat)); (default (BV 8 0) (bytes !! (index + 280)%nat))]))
    (Z_to_bv 32 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 281)%nat)); (default (BV 8 0) (bytes !! (index + 282)%nat)); (default (BV 8 0) (bytes !! (index + 283)%nat)); (default (BV 8 0) (bytes !! (index + 284)%nat))])) (default (BV 8 0) (bytes !! (index + 264)%nat))
    base bytes index (transactionPrepareRetained sp row chain chainTag bytes index
      (transactionTypeSourceCaller sp oldra (default (BV 8 0) (bytes !! (index + 264)%nat)) tail P)) -∗
  transactionTypeOutputEntry (sp + BV 64 1744)%bv oldra (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 271)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 272)%nat)) * 16777216)) (default (BV 8 0) (bytes !! (index + 264)%nat)) tail
    (transactionTypeSourceRetained sp row chain chainTag base bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionPreparePost /transactionPrepareRetained /transactionPrepareRegisters
    /transactionStoredSignatureTail /transactionSignatureStackFrame /transactionRecipientAssemblyStackContents
    /transactionRecipientAssemblyFields /transactionSignatureFieldRetained /transactionGasSignatureRetained
    /transactionTypeSourceCaller) in "Hpost".
  zesu_open_resource_groups.
  assert (Hdata : (bv_unsigned (sp + BV 64 1744)%bv = bv_unsigned sp + 1744)%Z).
  { match goal with Hlow : (0x20000000 <= bv_unsigned sp)%Z,
      Hhigh : (bv_unsigned sp + 1745 < 0x40000000)%Z |- _ => clear -Hlow Hhigh; bv_solve end. }
  rewrite /transactionTypeOutputEntry Hdata mem_mapsto_array_singleton
    /transactionTypeSourceRetained /transactionTypeSourceRegisters /transactionStoredSignatureTail
    /transactionSignatureStackFrame /transactionRecipientAssemblyStackContents /transactionRecipientAssemblyFields
    /transactionSignatureFieldRetained /transactionGasSignatureRetained.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_prepare_type_source_entry.
