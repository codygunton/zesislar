Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsFlagLoads WriteSuccessExactStorageKeysPairs16
  WriteSuccessExactStorageKeysPairHandoff WriteSuccessExactStorageKeysLoads8
  WriteSuccessExactStorageKeysLoadHandoff WriteSuccessExactStorageKeysUpperLoadHandoff
  WriteSuccessExactStorageKeysLowerLoadHandoff WriteSuccessExactStorageKeysInitialLoads.

Definition storageKeysPairs16Carry `{!islaG Sigma} `{!threadG}
    (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  (⌜(index + 32 <= length bytes)%nat⌝ ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 16) + bv_unsigned (storageKeyByte bytes index 17) * 256)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 18) * 65536 + bv_unsigned (storageKeyByte bytes index 19) * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 20) + bv_unsigned (storageKeyByte bytes index 21) * 256)) ∗
   "x9" ↦ᵣ RVal_Bits (transactionRowByte bytes index 22) ∗
   "x25" ↦ᵣ RVal_Bits (transactionRowByte bytes index 23) ∗
   storageKeysLoaded28Frame bytes index
     (storageKeysLoaded24Frame bytes index (storageKeysLoaded4Frame bytes index
       ("x24" ↦ᵣ RVal_Bits (transactionRowByte bytes index 12) ∗
        "x20" ↦ᵣ RVal_Bits (transactionRowByte bytes index 13) ∗
        "x18" ↦ᵣ RVal_Bits (transactionRowByte bytes index 14) ∗
        "x23" ↦ᵣ RVal_Bits (transactionRowByte bytes index 15) ∗ P ∗ True))) ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysPairs16Carry) := I.

Lemma storage_keys_pairs16_to_load8 `{!islaG Sigma} `{!threadG}
    row base bytes index (old21 : bv 64) (P : iProp Sigma) :
  storageKeysPairs16Post
    (storageKeyByte bytes index 16) (storageKeyByte bytes index 17)
    (storageKeyByte bytes index 18) (storageKeyByte bytes index 19)
    (storageKeyByte bytes index 20) (storageKeyByte bytes index 21)
    (storageKeysPairs16Frame row base bytes index ("x21" ↦ᵣ RVal_Bits old21 ∗ P ∗ True)%I) -∗
  storageKeysLoads8Entry row base bytes index (storageKeysPairs16Carry bytes index P).
Proof.
  iIntros "Hpost".
  iEval (unfold storageKeysPairs16Post, storageKeysPairs16Frame) in "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H6 & H7 & H28 & H1 & H8 & H26 & (Hrow & Harray & %Hcursor & %Hbound & %Hlow & %Hhigh & H9 & H25 & Hrest & _) & _)".
  iEval (unfold storageKeysLoaded28Frame, storageKeysLoaded24Frame,
    storageKeysLoaded4Frame) in "Hrest".
  iDestruct "Hrest" as
    "(H10 & H14 & H13 & H12 & (H11 & H5 & H17 & H16 & (H15 & H31 & H30 & H29 & (H24 & H20 & H18 & H23 & (H21 & HP & _) & _) & _) & _) & _)".
  iAssert (reg_col [(KindReg "x8", BitsShape 64); (KindReg "x26", BitsShape 64);
    (KindReg "x1", BitsShape 64); (KindReg "x21", BitsShape 64)])
    with "[H8 H26 H1 H21]" as "Hregs".
  { rewrite !reg_col_cons reg_col_nil. iSplitL "H8".
    { iExists _. iFrame. done. }
    iSplitL "H26". { iExists _. iFrame. done. }
    iSplitL "H1". { iExists _. iFrame. done. }
    iSplitL "H21". { iExists _. iFrame. done. } done. }
  iEval (unfold storageKeysLoads8Entry, storageKeysPairs16Carry,
    storageKeysLoaded28Frame, storageKeysLoaded24Frame, storageKeysLoaded4Frame).
  iFrame. iPureIntro. lia.
Qed.
Print Assumptions storage_keys_pairs16_to_load8.
