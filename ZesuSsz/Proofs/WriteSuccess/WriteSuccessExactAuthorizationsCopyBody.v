Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsLoopSpec WriteSuccessExactAuthorizationsCopy
  WriteSuccessExactAuthorizationsBody WriteSuccessExactAuthorizationsFacts
  WriteSuccessExactAuthorizationsModel.

Lemma authorization_copy_to_body `{!islaG Sigma} `{!threadG}
    sp pointer old5 base rows prefix row rest source tail (P : iProp Sigma) :
  authorizationCopyPost sp pointer base (144 * length prefix) source
    (authorizationCopyCallerFrame sp pointer old5 base rows prefix row rest source tail P) -∗
  authorizationBodyEntry sp (BV 64 0x155a4) old5 row
    (writeSuccessExactAuthorizationEvents sp rest tail)
    (authorizationBodyFrame sp pointer base rows prefix row rest source tail P).
Proof.
  iIntros "Hpost". iDestruct "Hpost" as (final13 final14)
    "(Hsys & H1 & H10 & H11 & H12 & H13 & H14 & H15 & Hsource & Hcopied & Hframe & _)".
  iDestruct "Hframe" as "(Hsp & H9 & Hcaller & _)".
  iDestruct "Hcaller" as "(H5 & H8 & H18 & Hscratch & Hmmio & Htrace & HP & %Hfacts & Hexit & _)".
  pose proof (authorization_facts_layout sp pointer base rows prefix row rest source Hfacts)
    as (Hprefix & Hrow & Hslice & HsourceLength).
  pose proof Hfacts as HfactsCopy.
  destruct Hfacts as (Hrows & Hall & Hbytes & Hposition & Hcount & Halign & Hlow & Hhigh & Hbase & Hend).
  have HcopyBase : bv_unsigned (sp + BV 64 1744)%bv = (bv_unsigned sp + 1744)%Z by bv_solve.
  iEval (rewrite Hslice HcopyBase) in "Hcopied".
  iAssert (reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
    (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)])
    with "[H10 H11 H12 H13]" as "Hwords".
  { rewrite !reg_col_cons reg_col_nil. iSplitL "H10".
    - iExists _. iFrame. done.
    - iSplitL "H11".
      + iExists _. iFrame. done.
      + iSplitL "H12".
        * iExists _. iFrame. done.
        * iSplit; last done. iExists _. iFrame. done. }
  iAssert (reg_col [(KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)])
    with "[H14 H15]" as "Hother".
  { rewrite !reg_col_cons reg_col_nil. iSplitL "H14".
    - iExists _. iFrame. done.
    - iSplit; last done. iExists _. iFrame. done. }
  unfold authorizationBodyEntry. iFrame "Hsys Hsp H1 H5 H8 Hwords Hcopied Hscratch Hmmio Htrace".
  iSplit; first done. iSplit; first done. iSplit; first done. iSplit; first done.
  unfold authorizationBodyFrame. iFrame. iPureIntro. exact HfactsCopy.
Qed.
Print Assumptions authorization_copy_to_body.
