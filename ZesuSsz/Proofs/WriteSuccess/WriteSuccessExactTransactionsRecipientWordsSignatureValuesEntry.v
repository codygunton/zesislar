Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.RegPacking.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsValueMiddleWordsEntry WriteSuccessExactTransactionsRecipientWords
  WriteSuccessExactTransactionsSignatureValues WriteSuccessExactTransactionsRecipientTagShiftEntry
  WriteSuccessExactTransactionsSignatureFieldEntry WriteSuccessExactTransactionsGasSignatureEntry
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsFlagLoads.
Local Open Scope Z_scope.

Definition transactionSignatureValuesCaller `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col [(KindReg "x21", BitsShape 64)] ∗
   (bv_unsigned sp + 144) ↦ₘ? 16 ∗ (bv_unsigned sp + 216) ↦ₘ? 8 ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureValuesCaller) := I.

Definition transactionSignatureValuesRetained `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 281)%nat)); (default (BV 8 0) (bytes !! (index + 282)%nat)); (default (BV 8 0) (bytes !! (index + 283)%nat)); (default (BV 8 0) (bytes !! (index + 284)%nat))])) ∗
   "x15" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 273)%nat)); (default (BV 8 0) (bytes !! (index + 274)%nat)); (default (BV 8 0) (bytes !! (index + 275)%nat)); (default (BV 8 0) (bytes !! (index + 276)%nat))])) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 275)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 276)%nat)) * 16777216)) ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 277)%nat)) + bv_unsigned (default (BV 8 0) (bytes !! (index + 278)%nat)) * 256)) ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 277)%nat)); (default (BV 8 0) (bytes !! (index + 278)%nat)); (default (BV 8 0) (bytes !! (index + 279)%nat)); (default (BV 8 0) (bytes !! (index + 280)%nat))])) ∗
   "x29" ↦ᵣ RVal_Bits (transactionRowWord bytes index 64) ∗
   "x30" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 271)%nat)) * 65536)) ∗
   "x5" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 271)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 272)%nat)) * 16777216)) ∗
   (bv_unsigned sp + 128) ↦ₘ (transactionRowWord bytes index 64) ∗
   transactionRecipientMiddleFixedRegisters bytes index
     (transactionRecipientAssemblyStackContents sp row chain chainTag bytes index P) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureValuesRetained) := I.

Lemma transactions_recipient_words_signature_values_entry `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base bytes index (P : iProp Sigma) :
  transactionRecipientWordsPost
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
    (transactionRecipientWordsRetained sp row chain chainTag base bytes index (transactionSignatureValuesCaller sp P)) -∗
  transactionSignatureValuesEntry sp row base bytes index
    (transactionSignatureValuesRetained sp row chain chainTag bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionRecipientWordsPost) in "Hpost".
  iDestruct "Hpost" as "(Hsys & H14 & H15 & H16 & H17 & H6 & H13 & Hframe & _)".
  iEval (rewrite /transactionRecipientWordsRetained /transactionRecipientMiddleStableFrame
    /transactionRecipientMiddleFixedRegisters /transactionRecipientAssemblyStackContents
    /transactionRecipientAssemblyFields /transactionSignatureFieldRetained
    /transactionGasSignatureRetained) in "Hframe".
  zesu_open_resource_groups.
  iSelect (transactionSignatureValuesCaller sp P) ltac:(fun Hcaller =>
    iDestruct Hcaller as "(H21 & H144 & H216 & HP & _)").
  iAssert (reg_col [(KindReg "x21", BitsShape 64); (KindReg "x16", BitsShape 64)])%I
    with "[H16 H21]" as "Hregs".
  { iApply (reg_col_mixed_collect
      [("x16", Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 273)%nat)) + bv_unsigned (default (BV 8 0) (bytes !! (index + 274)%nat)) * 256))]
      [] [(KindReg "x21", BitsShape 64)]).
    - solve_Permutation.
    - iFrame. rewrite big_sepL_nil reg_col_nil. done. }
  rewrite /transactionSignatureValuesEntry /transactionSignatureValuesRetained
    /transactionRecipientMiddleFixedRegisters /transactionRecipientAssemblyStackContents
    /transactionRecipientAssemblyFields /transactionSignatureFieldRetained /transactionGasSignatureRetained.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_recipient_words_signature_values_entry.

