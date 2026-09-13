Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysPairHandoff.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactBlobHashesInitialLoads WriteSuccessExactBlobHashesSaveLoads12
  WriteSuccessExactBlobHashesLoadHandoff WriteSuccessExactBlobHashesUpperLoadHandoff
  WriteSuccessExactBlobHashesLowerLoadHandoff WriteSuccessExactBlobHashesPairsLoad16.

Definition blobPairs16RemainingFrame `{!islaG Sigma} `{!threadG}
    (count : bv 64) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  ("x27" ↦ᵣ RVal_Bits count ∗
   "x20" ↦ᵣ RVal_Bits (transactionRowByte bytes index 22) ∗
   "x21" ↦ᵣ RVal_Bits (transactionRowByte bytes index 23) ∗
   blobLoaded28Frame bytes index (blobLoaded24Frame bytes index
     (blobLoaded4Frame bytes index
       ("x22" ↦ᵣ RVal_Bits (transactionRowByte bytes index 12) ∗
        "x23" ↦ᵣ RVal_Bits (transactionRowByte bytes index 13) ∗
        "x24" ↦ᵣ RVal_Bits (transactionRowByte bytes index 14) ∗ P ∗ True)%I)) ∗ True)%I.
Global Instance : LithiumUnfold (@blobPairs16RemainingFrame) := I.

Lemma blob_initial_loads_to_pairs16 `{!islaG Sigma} `{!threadG}
    row count base bytes index (P : iProp Sigma) :
  blobSaveLoads12Post row count base bytes index
    (blobLoaded4Frame bytes index (blobLoaded24Frame bytes index
      (blobLoaded28Frame bytes index (blobLoaded20Frame bytes index
        (blobLoaded16Frame bytes index
          (⌜(index + 32 <= length bytes)%nat⌝ ∗
           reg_col [(KindReg "x25", BitsShape 64)] ∗ P ∗ True)%I))))) -∗
  blobPairs16Entry
    (storageKeyByte bytes index 16) (storageKeyByte bytes index 17)
    (storageKeyByte bytes index 18) (storageKeyByte bytes index 19)
    (storageKeyByte bytes index 20) (storageKeyByte bytes index 21)
    (blobByte15EntryFrame row base bytes index
      (blobPairs16RemainingFrame count bytes index
        (⌜(index + 32 <= length bytes)%nat⌝ ∗ P ∗ True)%I)).
Proof.
  iIntros "Hfirst".
  iEval (unfold blobSaveLoads12Post, blobLoaded4Frame, blobLoaded24Frame,
    blobLoaded28Frame, blobLoaded20Frame, blobLoaded16Frame) in "Hfirst".
  iDestruct "Hfirst" as
    "(Hsys & Hcount & H22 & H23 & H24 & Hrow & Harray & %Hcursor & %Hbound & %Hlow & %Hhigh &
      (H15 & H31 & H30 & H29 & (H11 & H5 & H17 & H16 & (H10 & H14 & H13 & H12 &
        (H9 & H18 & H20 & H21 & (H6 & H7 & H28 & H8 & HP & _) & _) & _) & _) & _) & _)".
  iDestruct "HP" as "(%Hbound32 & H25 & HP & _)".
  iEval (unfold blobPairs16Entry).
  iEval (rewrite
    -(storage_keys_row_byte bytes index 16 ltac:(lia))
    -(storage_keys_row_byte bytes index 17 ltac:(lia))
    -(storage_keys_row_byte bytes index 18 ltac:(lia))
    -(storage_keys_row_byte bytes index 19 ltac:(lia))
    -(storage_keys_row_byte bytes index 20 ltac:(lia))
    -(storage_keys_row_byte bytes index 21 ltac:(lia))).
  iEval (unfold blobByte15EntryFrame, blobPairs16RemainingFrame,
    blobLoaded28Frame, blobLoaded24Frame, blobLoaded4Frame).
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions blob_initial_loads_to_pairs16.
