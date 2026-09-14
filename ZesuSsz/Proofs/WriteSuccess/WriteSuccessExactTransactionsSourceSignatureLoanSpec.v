Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessAccessListsSpec WriteSuccessStorageKeysSpec
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsFlagLoads
  WriteSuccessExactBlobHashesAuthorizationEntry
  WriteSuccessExactTransactionsSourceFieldLayout.

From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessExactTransactionsSourceBlobFeeFrame.

Definition transactionSourceSignatureWords `{!islaG Sigma}
    (sp : bv 64) (bytes : list (bv 8)) (index : nat) : iProp Sigma :=
  ((bv_unsigned sp + 176) ↦ₘ transactionRowWord bytes index 256 ∗
   (bv_unsigned sp + 184) ↦ₘ transactionRowWord bytes index 120 ∗
   (bv_unsigned sp + 192) ↦ₘ transactionRowWord bytes index 112 ∗
   (bv_unsigned sp + 200) ↦ₘ transactionRowWord bytes index 104 ∗
   (bv_unsigned sp + 208) ↦ₘ transactionRowWord bytes index 128 ∗
   (bv_unsigned sp + 216) ↦ₘ transactionRowWord bytes index 96 ∗
   (bv_unsigned sp + 224) ↦ₘ transactionRowWord bytes index 152 ∗
   (bv_unsigned sp + 232) ↦ₘ transactionRowWord bytes index 144 ∗
   (bv_unsigned sp + 240) ↦ₘ transactionRowWord bytes index 136 ∗ True)%I.

Definition transactionSourceSignatureRemainingShapes : list (reg_kind * valu_shape) :=
  list_delete 6%nat (list_delete 6%nat blobAuthorizationRemainingShapes).

Definition transactionSourceSignatureRemainder `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (bytes : list (bv 8)) (processed index : nat)
    (dataBytes accessBytes chainBytes : list (bv 8))
    (entries : list writeSuccessAccessEntry) (blobBytes : list (bv 8))
    (Q : iProp Sigma) : iProp Sigma :=
  (∃ pointer storedIndex : bv 64,
   "x19" ↦ᵣ RVal_Bits pointer ∗ "x22" ↦ᵣ RVal_Bits (BV 64 0) ∗
   reg_col transactionSourceSignatureRemainingShapes ∗
   writeSuccessByteArrayOwn (transactionRowWord bytes index 224) blobBytes ∗
   (bv_unsigned sp + 136) ↦ₘ transactionRowWord bytes index 232 ∗
   bv_unsigned (transactionRowWord bytes index 208) ↦ₘ∗ accessBytes ∗
   writeSuccessAccessEntriesOwn entries ∗
   (bv_unsigned sp + 256) ↦ₘ transactionRowWord bytes index 208 ∗
   (bv_unsigned sp + 264) ↦ₘ Z_to_bv 64 (Z.of_nat (length entries)) ∗
   (bv_unsigned sp + 272) ↦ₘ storedIndex ∗
   (bv_unsigned sp + 1744) ↦ₘ? 40 ∗ writeSuccessStorageKeysScratch sp ∗
   (bv_unsigned sp + 1640) ↦ₘ transactionRecipientSourceWord bytes index 265 ∗
   (bv_unsigned sp + 1648) ↦ₘ transactionRecipientSourceWord bytes index 273 ∗
   (bv_unsigned sp + 1656) ↦ₘ transactionRecipientSourceLast bytes index ∗
   (bv_unsigned sp + 120) ↦ₘ transactionRowByte bytes index 285 ∗
   (bv_unsigned sp + 128) ↦ₘ transactionRowWord bytes index 64 ∗
   bv_unsigned (transactionRowWord bytes index 192) ↦ₘ∗ dataBytes ∗
   bv_unsigned (sp + BV 64 1664)%bv ↦ₘ∗ chainBytes ∗
   base ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 248) ↦ₘ Z_to_bv 64 (Z.of_nat processed) ∗
   (bv_unsigned sp + 168) ↦ₘ transactionRowWord bytes index 240 ∗
   (bv_unsigned sp + 1660) ↦ₘ? 4 ∗
   (bv_unsigned sp + 1680) ↦ₘ? 32 ∗
   (bv_unsigned sp + 1784) ↦ₘ? 112 ∗
   ⌜dataBytes <> [] -> mapRamBase defaultMap <= bv_unsigned (transactionRowWord bytes index 192) /\
     bv_unsigned (transactionRowWord bytes index 192) + Z.of_nat (length dataBytes) < machineRamEnd defaultMap⌝ ∗
   ⌜accessBytes <> [] -> mapRamBase defaultMap <= bv_unsigned (transactionRowWord bytes index 208) /\
     bv_unsigned (transactionRowWord bytes index 208) + Z.of_nat (length accessBytes) < machineRamEnd defaultMap⌝ ∗
   Q ∗ True)%I.

Definition transactionSourceSignatureLoan `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (bytes : list (bv 8)) (processed index : nat)
    (dataBytes accessBytes chainBytes : list (bv 8))
    (entries : list writeSuccessAccessEntry) (blobBytes : list (bv 8))
    (Q : iProp Sigma) : iProp Sigma :=
  (reg_col [(KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)] -∗
   transactionSourceSignatureWords sp bytes index -∗
   (bv_unsigned sp - 48) ↦ₘ? 16 -∗
   transactionSourceBlobFeeRetained sp base bytes processed index dataBytes accessBytes
     chainBytes entries blobBytes Q)%I.

Definition transactionSourceSignatureCommonFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (index : nat) : iProp Sigma :=
  ("x18" ↦ᵣ RVal_Bits (BV 64 0) ∗
   (bv_unsigned sp + 144) ↦ₘ transactionRowWord bytes index 88 ∗
   (bv_unsigned sp + 152) ↦ₘ transactionRowWord bytes index 80 ∗
   (bv_unsigned sp + 160) ↦ₘ transactionRowWord bytes index 248 ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSourceSignatureWords) := I.
Global Instance : LithiumUnfold (@transactionSourceSignatureRemainder) := I.
Global Instance : LithiumUnfold (@transactionSourceSignatureLoan) := I.
Global Instance : LithiumUnfold (@transactionSourceSignatureCommonFrame) := I.

Lemma transactions_source_signature_register_factor `{!islaG Sigma} `{!threadG} :
  reg_col blobAuthorizationRemainingShapes ⊣⊢
  (reg_col [(KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)] ∗
   reg_col transactionSourceSignatureRemainingShapes)%I.
Proof.
  have H12 : blobAuthorizationRemainingShapes !! 6%nat = Some (KindReg "x12", BitsShape 64)
    by vm_compute.
  have H13 : (list_delete 6%nat blobAuthorizationRemainingShapes) !! 6%nat =
    Some (KindReg "x13", BitsShape 64) by vm_compute.
  iSplit.
  - iIntros "Hregs".
    iEval (rewrite (reg_col_lookup _ _ _ H12)) in "Hregs".
    iDestruct "Hregs" as (v12) "(%Hv12 & H12 & Hregs)".
    iEval (rewrite (reg_col_lookup _ _ _ H13)) in "Hregs".
    iDestruct "Hregs" as (v13) "(%Hv13 & H13 & Hregs)".
    iSplitL "H12 H13".
    { rewrite !reg_col_cons reg_col_nil.
      iSplitL "H12"; first (iExists v12; iFrame; done).
      iSplitL "H13"; last done. iExists v13; iFrame; done. }
    iExact "Hregs".
  - iIntros "[Hpair Hregs]".
    iEval (rewrite !reg_col_cons reg_col_nil) in "Hpair".
    iDestruct "Hpair" as "[H12 Htail]".
    iDestruct "H12" as (v12) "[%Hv12 H12]".
    iDestruct "Htail" as "[H13 _]".
    iDestruct "H13" as (v13) "[%Hv13 H13]".
    iEval (rewrite (reg_col_lookup _ _ _ H12)).
    iExists v12; iFrame "H12"; iSplit; first (iPureIntro; exact Hv12).
    iEval (rewrite (reg_col_lookup _ _ _ H13)).
    iExists v13; iFrame "H13"; iSplit; first (iPureIntro; exact Hv13).
    iExact "Hregs".
Qed.
Print Assumptions transactions_source_signature_register_factor.
