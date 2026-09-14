Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.RegPacking.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSignatureLowWideEntry WriteSuccessExactTransactionsRecipientWide
  WriteSuccessExactTransactionsSignatureSuffix WriteSuccessExactTransactionsSignatureTail
  WriteSuccessExactTransactionsValueMiddleWordsEntry WriteSuccessExactTransactionsRecipientTagShiftEntry
  WriteSuccessExactTransactionsSignatureFieldEntry WriteSuccessExactTransactionsGasSignatureEntry
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsFlagLoads.
Local Open Scope Z_scope.

Definition transactionSignatureSuffixCaller `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 192) ↦ₘ? 16 ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureSuffixCaller) := I.

Definition transactionSignatureTailCaller `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 184) ↦ₘ? 8 ∗ (bv_unsigned sp + 208) ↦ₘ? 8 ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureTailCaller) := I.

Definition transactionSignatureStackFrame `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x21" ↦ᵣ RVal_Bits (transactionRowWord bytes index 72) ∗
   (bv_unsigned sp + 128) ↦ₘ (transactionRowWord bytes index 64) ∗
   (bv_unsigned sp + 144) ↦ₘ (transactionRowWord bytes index 88) ∗
   (bv_unsigned sp + 152) ↦ₘ (transactionRowWord bytes index 80) ∗
   (bv_unsigned sp + 216) ↦ₘ (transactionRowWord bytes index 96) ∗
   transactionRecipientAssemblyStackContents sp row chain chainTag bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureStackFrame) := I.

Definition transactionSignatureSuffixRetained `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 265)%nat)); (default (BV 8 0) (bytes !! (index + 266)%nat)); (default (BV 8 0) (bytes !! (index + 267)%nat)); (default (BV 8 0) (bytes !! (index + 268)%nat)); (default (BV 8 0) (bytes !! (index + 269)%nat)); (default (BV 8 0) (bytes !! (index + 270)%nat)); (default (BV 8 0) (bytes !! (index + 271)%nat)); (default (BV 8 0) (bytes !! (index + 272)%nat))])) ∗
   "x16" ↦ᵣ RVal_Bits (Z_to_bv 64
     (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 269)%nat)); (default (BV 8 0) (bytes !! (index + 270)%nat)); (default (BV 8 0) (bytes !! (index + 271)%nat)); (default (BV 8 0) (bytes !! (index + 272)%nat))] * 4294967296)) ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 273)%nat)); (default (BV 8 0) (bytes !! (index + 274)%nat)); (default (BV 8 0) (bytes !! (index + 275)%nat)); (default (BV 8 0) (bytes !! (index + 276)%nat)); (default (BV 8 0) (bytes !! (index + 277)%nat)); (default (BV 8 0) (bytes !! (index + 278)%nat)); (default (BV 8 0) (bytes !! (index + 279)%nat)); (default (BV 8 0) (bytes !! (index + 280)%nat))])) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 267)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 268)%nat)) * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 269)%nat)) + bv_unsigned (default (BV 8 0) (bytes !! (index + 270)%nat)) * 256)) ∗
   "x5" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 271)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 272)%nat)) * 16777216)) ∗
   transactionRecipientWideRegisters bytes index
     (transactionSignatureStackFrame sp row chain chainTag bytes index P) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureSuffixRetained) := I.

Definition transactionSignatureTailRetained `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) bytes index (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 192) ↦ₘ (transactionRowWord bytes index 112) ∗
   (bv_unsigned sp + 200) ↦ₘ (transactionRowWord bytes index 104) ∗
   transactionSignatureSuffixRetained sp row chain chainTag bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureTailRetained) := I.

Lemma transactions_recipient_wide_signature_suffix_entry `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base bytes index (P : iProp Sigma) :
  transactionRecipientWidePost
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
    (transactionRecipientWideFrame sp row chain chainTag base bytes index (transactionSignatureSuffixCaller sp P)) -∗
  transactionSignatureSuffixEntry sp row base bytes index
    (transactionSignatureSuffixRetained sp row chain chainTag bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionRecipientWidePost) in "Hpost".
  iDestruct "Hpost" as "(Hsys & H12 & H16 & H15 & H13 & Hframe & _)".
  iPoseProof (reg_col_bv_list_shape
    [("x15", Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 273)%nat)); (default (BV 8 0) (bytes !! (index + 274)%nat)); (default (BV 8 0) (bytes !! (index + 275)%nat)); (default (BV 8 0) (bytes !! (index + 276)%nat))]))]
    with "[H15]") as "Hregs".
  { cbn. iFrame. }
  iEval (rewrite /transactionRecipientWideFrame /transactionRecipientWideRegisters
    /transactionSignatureAssemblyStorage /transactionRecipientAssemblyStackContents
    /transactionRecipientAssemblyFields /transactionSignatureFieldRetained
    /transactionGasSignatureRetained /transactionSignatureSuffixCaller) in "Hframe".
  zesu_open_resource_groups.
  rewrite /transactionSignatureSuffixEntry /transactionSignatureSuffixRetained
    /transactionRecipientWideRegisters /transactionSignatureStackFrame /transactionRecipientAssemblyStackContents
    /transactionRecipientAssemblyFields /transactionSignatureFieldRetained /transactionGasSignatureRetained.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_recipient_wide_signature_suffix_entry.

Lemma transactions_signature_suffix_tail_entry `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base bytes index (P : iProp Sigma) :
  transactionSignatureSuffixPost sp row base bytes index
    (transactionSignatureSuffixRetained sp row chain chainTag bytes index (transactionSignatureTailCaller sp P)) -∗
  transactionSignatureTailEntry sp row base bytes index
    (transactionSignatureTailRetained sp row chain chainTag bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionSignatureSuffixPost) in "Hpost".
  iDestruct "Hpost" as "(Hsys & Hsp & Hrow & H15 & Hframe)".
  iPoseProof (reg_col_bv_list_shape [("x15", transactionRowWord bytes index 112)]
    with "[H15]") as "Hregs".
  { cbn. iFrame. }
  iEval (rewrite /transactionSignatureSuffixRetained /transactionRecipientWideRegisters
    /transactionSignatureStackFrame /transactionRecipientAssemblyStackContents
    /transactionRecipientAssemblyFields /transactionSignatureFieldRetained
    /transactionGasSignatureRetained /transactionSignatureTailCaller) in "Hframe".
  zesu_open_resource_groups.
  rewrite /transactionSignatureTailEntry /transactionSignatureTailRetained /transactionSignatureSuffixRetained
    /transactionRecipientWideRegisters /transactionSignatureStackFrame /transactionRecipientAssemblyStackContents
    /transactionRecipientAssemblyFields /transactionSignatureFieldRetained /transactionGasSignatureRetained.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_signature_suffix_tail_entry.

