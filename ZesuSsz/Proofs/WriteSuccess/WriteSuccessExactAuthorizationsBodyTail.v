Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.ArrayForget.
Require Import ZesuSsz.Automation.RegCollections.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsLoopSpec WriteSuccessExactAuthorizationsBodyPost
  WriteSuccessExactAuthorizationsU256 WriteSuccessExactAuthorizationsTail
  WriteSuccessExactAuthorizationsModel.

Lemma authorization_body_to_tail `{!islaG Sigma} `{!threadG}
    sp pointer base rows prefix row rest source tail (P : iProp Sigma) :
  authorizationBodyPost sp row (writeSuccessExactAuthorizationEvents sp rest tail)
    (authorizationBodyFrame sp pointer base rows prefix row rest source tail P) -∗
  authorizationTailState pointer (Z_to_bv 64 (Z.of_nat (S (length rest))))
    (authorizationTailPayload sp pointer base rows prefix row rest source tail P).
Proof.
  iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H8 & H10 & H11 & Hpair & Hscratch & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hcopied & %Hlen & %Halign & %Hlow & %Hhigh & Hcaller & _)".
  iDestruct "Hcaller" as "(H9 & H18 & Hother & Hsource & HP & %Hfacts & Hexit & _)".
  iPoseProof (byte_array_forget with "Hcopied") as "Hcopy". iEval (rewrite Hlen /=) in "Hcopy".
  iAssert (reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64)])
    with "[H10 H11]" as "Hknown".
  { rewrite !reg_col_cons reg_col_nil. iSplitL "H10".
    - iExists _. iFrame. done.
    - iSplit; last done. iExists _. iFrame. done. }
  iPoseProof (zesu_reg_col_append with "[$Hknown $Hpair]") as "Hwords".
  iPoseProof (zesu_reg_col_append with "[$Hwords $Hother]") as "Hregs".
  unfold authorizationTailState, authorizationTailPayload. iFrame. done.
Qed.
Print Assumptions authorization_body_to_tail.
