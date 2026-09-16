Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsFlagLoads WriteSuccessExactStorageKeysPairs8
  WriteSuccessExactStorageKeysPairHandoff WriteSuccessExactStorageKeysLoads0
  WriteSuccessExactStorageKeysUpperLoadHandoff WriteSuccessExactStorageKeysLowerLoadHandoff
  WriteSuccessExactStorageKeysPairs8Handoff WriteSuccessExactStorageKeysInitialLoads.

Definition storageKeysPairs8Carry `{!islaG Sigma} `{!threadG}
    (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  (⌜(index + 32 <= length bytes)%nat⌝ ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 8) + bv_unsigned (storageKeyByte bytes index 9) * 256)) ∗
   "x21" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 10) * 65536 + bv_unsigned (storageKeyByte bytes index 11) * 16777216)) ∗
   "x20" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 12) + bv_unsigned (storageKeyByte bytes index 13) * 256)) ∗
   "x9" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 22) * 65536 + bv_unsigned (storageKeyByte bytes index 23) * 16777216)) ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 16) + bv_unsigned (storageKeyByte bytes index 17) * 256)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 18) * 65536 + bv_unsigned (storageKeyByte bytes index 19) * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 20) + bv_unsigned (storageKeyByte bytes index 21) * 256)) ∗
   storageKeysLoaded28Frame bytes index
     (storageKeysLoaded24Frame bytes index (storageKeysLoaded4Frame bytes index
       ("x18" ↦ᵣ RVal_Bits (transactionRowByte bytes index 14) ∗
        "x23" ↦ᵣ RVal_Bits (transactionRowByte bytes index 15) ∗ P ∗ True))) ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysPairs8Carry) := I.

Lemma storage_keys_pairs8_to_load0 `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  storageKeysPairs8Post
    (storageKeyByte bytes index 8) (storageKeyByte bytes index 9)
    (storageKeyByte bytes index 10) (storageKeyByte bytes index 11)
    (storageKeyByte bytes index 12) (storageKeyByte bytes index 13)
    (storageKeyByte bytes index 22) (storageKeyByte bytes index 23)
    (storageKeysPairs8Frame row base bytes index P) -∗
  storageKeysLoads0Entry row base bytes index (storageKeysPairs8Carry bytes index P).
Proof.
  iIntros "Hpost".
  iEval (unfold storageKeysPairs8Post, storageKeysPairs8Frame) in "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H8 & H26 & H1 & H21 & H24 & H20 & H9 & H25 & (Hrow & Harray & %Hcursor & %Hbound & %Hlow & %Hhigh & H6 & H7 & H28 & Hrest & _) & _)".
  iAssert (reg_col [(KindReg "x24", BitsShape 64); (KindReg "x25", BitsShape 64);
    (KindReg "x26", BitsShape 64); (KindReg "x1", BitsShape 64)])
    with "[H24 H25 H26 H1]" as "Hregs".
  { rewrite !reg_col_cons reg_col_nil. iSplitL "H24".
    { iExists _. iFrame. done. }
    iSplitL "H25". { iExists _. iFrame. done. }
    iSplitL "H26". { iExists _. iFrame. done. }
    iSplitL "H1". { iExists _. iFrame. done. } done. }
  iEval (unfold storageKeysLoads0Entry, storageKeysPairs8Carry).
  iFrame. iPureIntro. lia.
Qed.
Print Assumptions storage_keys_pairs8_to_load0.
