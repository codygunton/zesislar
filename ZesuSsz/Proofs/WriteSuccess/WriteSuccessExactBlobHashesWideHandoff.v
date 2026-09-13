Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysPairHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysWords.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactBlobHashesUpperWords WriteSuccessExactBlobHashesUpperWordsHandoff
  WriteSuccessExactBlobHashesLowerWords WriteSuccessExactBlobHashesWide.

Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBlobHashesLowerWordsHandoff.

Lemma blob_lower_words_to_wide `{!islaG Sigma} `{!threadG}
    row count base bytes index (P : iProp Sigma) :
  blobLowerWordsPost (storageKeyByte bytes index 0) (storageKeyByte bytes index 1) (storageKeyByte bytes index 2) (storageKeyByte bytes index 3) (storageKeyByte bytes index 4) (storageKeyByte bytes index 5) (storageKeyByte bytes index 6) (storageKeyByte bytes index 7) (storageKeyByte bytes index 24) (storageKeyByte bytes index 25) (storageKeyByte bytes index 26) (storageKeyByte bytes index 27) (storageKeyByte bytes index 28) (storageKeyByte bytes index 29) (storageKeyByte bytes index 30) (storageKeyByte bytes index 31)
    (blobLowerWordsFrame row count base bytes index P) -∗
  blobFourWordsPost row count base bytes index P.
Proof.
  iIntros "Hpost".
  iEval (unfold blobLowerWordsPost, blobLowerWordsFrame) in "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H5 & H15 & H11 & H10 & H21 & H22 & H29 & H16 & H12 &
      (H13 & H14 & H8 & H17 & H6 & H7 & H28 & H20 & H9 & H18 & H24 & H25 & H23 & H26 & H31 & H30 & Hframe & _) & _)".
  iAssert (reg_col ((λ r, (KindReg r, BitsShape 64)) <$>
    ["x6"; "x7"; "x9"; "x12"; "x16"; "x18"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x28"; "x29"; "x30"; "x31"]))
    with "[H6 H7 H9 H12 H16 H18 H20 H21 H22 H23 H24 H25 H26 H28 H29 H30 H31]" as "Hregs".
  { cbn [fmap]. rewrite !reg_col_cons reg_col_nil.
    iSplitL "H6". { iExists _. iFrame. done. }
    iSplitL "H7". { iExists _. iFrame. done. }
    iSplitL "H9". { iExists _. iFrame. done. }
    iSplitL "H12". { iExists _. iFrame. done. }
    iSplitL "H16". { iExists _. iFrame. done. }
    iSplitL "H18". { iExists _. iFrame. done. }
    iSplitL "H20". { iExists _. iFrame. done. }
    iSplitL "H21". { iExists _. iFrame. done. }
    iSplitL "H22". { iExists _. iFrame. done. }
    iSplitL "H23". { iExists _. iFrame. done. }
    iSplitL "H24". { iExists _. iFrame. done. }
    iSplitL "H25". { iExists _. iFrame. done. }
    iSplitL "H26". { iExists _. iFrame. done. }
    iSplitL "H28". { iExists _. iFrame. done. }
    iSplitL "H29". { iExists _. iFrame. done. }
    iSplitL "H30". { iExists _. iFrame. done. }
    iSplitL "H31". { iExists _. iFrame. done. }
    done. }
  iEval (unfold blobFourWordsPost, storageKeyFour; cbn [Nat.add]).
  iFrame.
Qed.
Print Assumptions blob_lower_words_to_wide.
