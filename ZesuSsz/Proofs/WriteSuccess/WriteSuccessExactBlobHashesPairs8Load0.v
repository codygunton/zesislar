Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysPairHandoff.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsFlagLoads WriteSuccessExactBlobHashesPairs8
  WriteSuccessExactBlobHashesPairHandoff WriteSuccessExactBlobHashesLoads0
  WriteSuccessExactBlobHashesUpperLoadHandoff WriteSuccessExactBlobHashesLowerLoadHandoff
  WriteSuccessExactBlobHashesPairs8Handoff WriteSuccessExactBlobHashesInitialLoads.

Definition blobPairs8Carry `{!islaG Sigma} `{!threadG}
    (count : bv 64) (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  (⌜(index + 32 <= length bytes)%nat⌝ ∗ "x27" ↦ᵣ RVal_Bits count ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 8) + bv_unsigned (storageKeyByte bytes index 9) * 256)) ∗
   "x9" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 10) * 65536 + bv_unsigned (storageKeyByte bytes index 11) * 16777216)) ∗
   "x18" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 12) + bv_unsigned (storageKeyByte bytes index 13) * 256)) ∗
   "x20" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 22) * 65536 + bv_unsigned (storageKeyByte bytes index 23) * 16777216)) ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 16) + bv_unsigned (storageKeyByte bytes index 17) * 256)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 18) * 65536 + bv_unsigned (storageKeyByte bytes index 19) * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (storageKeyByte bytes index 20) + bv_unsigned (storageKeyByte bytes index 21) * 256)) ∗
   blobLoaded28Frame bytes index
     (blobLoaded24Frame bytes index (blobLoaded4Frame bytes index
       ("x24" ↦ᵣ RVal_Bits (transactionRowByte bytes index 14) ∗
        "x25" ↦ᵣ RVal_Bits (transactionRowByte bytes index 15) ∗ P ∗ True))) ∗ True)%I.
Global Instance : LithiumUnfold (@blobPairs8Carry) := I.


Lemma blob_pairs8_to_load0 `{!islaG Sigma} `{!threadG}
    row count base bytes index (P : iProp Sigma) :
  blobPairs8Post
    (storageKeyByte bytes index 8) (storageKeyByte bytes index 9)
    (storageKeyByte bytes index 10) (storageKeyByte bytes index 11)
    (storageKeyByte bytes index 12) (storageKeyByte bytes index 13)
    (storageKeyByte bytes index 22) (storageKeyByte bytes index 23)
    (blobPairs8Frame row count base bytes index P) -∗
  blobLoads0Entry row base bytes index (blobPairs8Carry count bytes index P).
Proof.
  iIntros "Hpost".
  iEval (unfold blobPairs8Post, blobPairs8Frame) in "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H8 & H9 & H18 & H26 & H22 & H23 & H20 & H21 &
      (Hrow & Hcount & Harray & %Hcursor & %Hbound & %Hlow & %Hhigh & H6 & H7 & H28 & Hrest & _) & _)".
  iAssert (reg_col [(KindReg "x21", BitsShape 64); (KindReg "x22", BitsShape 64);
    (KindReg "x23", BitsShape 64); (KindReg "x26", BitsShape 64)])
    with "[H21 H22 H23 H26]" as "Hregs".
  { rewrite !reg_col_cons reg_col_nil. iSplitL "H21".
    { iExists _. iFrame. done. }
    iSplitL "H22". { iExists _. iFrame. done. }
    iSplitL "H23". { iExists _. iFrame. done. }
    iSplitL "H26". { iExists _. iFrame. done. } done. }
  iEval (unfold blobLoads0Entry, blobPairs8Carry).
  iFrame. iPureIntro. lia.
Qed.
Print Assumptions blob_pairs8_to_load0.
