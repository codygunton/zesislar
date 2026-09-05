From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15674Boundary.

Lemma write_success_transactions_post_15674_saved_shapes
    `{!islaG Sigma} `{!threadG} (saved : list valu) :
  reg_col (zip_with (fun r v => (KindReg r, ExactShape v))
    writeSuccessTransactionsPost15674Saved saved) -∗
  ⌜length saved = 12%nat⌝ -∗
  ⌜Forall (fun v => valu_has_shape v (BitsShape 64)) saved⌝ -∗
  reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
    writeSuccessTransactionsPost15674Saved).
Proof.
  iStartProof. iIntros "Hsaved %Hlength %Hshapes".
  destruct saved as [|v8 saved]; cbn in Hlength; try lia.
  destruct saved as [|v9 saved]; cbn in Hlength; try lia.
  destruct saved as [|v18 saved]; cbn in Hlength; try lia.
  destruct saved as [|v19 saved]; cbn in Hlength; try lia.
  destruct saved as [|v20 saved]; cbn in Hlength; try lia.
  destruct saved as [|v21 saved]; cbn in Hlength; try lia.
  destruct saved as [|v22 saved]; cbn in Hlength; try lia.
  destruct saved as [|v23 saved]; cbn in Hlength; try lia.
  destruct saved as [|v24 saved]; cbn in Hlength; try lia.
  destruct saved as [|v25 saved]; cbn in Hlength; try lia.
  destruct saved as [|v26 saved]; cbn in Hlength; try lia.
  destruct saved as [|v27 saved]; cbn in Hlength; try lia.
  destruct saved as [|vrest rest]; cbn in Hlength; try lia.
  repeat rewrite Forall_cons_iff in Hshapes.
  destruct Hshapes as
    (Hv8 & Hv9 & Hv18 & Hv19 & Hv20 & Hv21 & Hv22 & Hv23 & Hv24 & Hv25 &
     Hv26 & Hv27 & _).
  iEval (unfold writeSuccessTransactionsPost15674Saved; cbn) in "Hsaved".
  iEval (unfold writeSuccessTransactionsPost15674Saved; cbn).
  iDestruct "Hsaved" as
    "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & _)".
  iDestruct "H8" as (a8) "(%Ha8 & H8)". subst a8.
  iDestruct "H9" as (a9) "(%Ha9 & H9)". subst a9.
  iDestruct "H18" as (a18) "(%Ha18 & H18)". subst a18.
  iDestruct "H19" as (a19) "(%Ha19 & H19)". subst a19.
  iDestruct "H20" as (a20) "(%Ha20 & H20)". subst a20.
  iDestruct "H21" as (a21) "(%Ha21 & H21)". subst a21.
  iDestruct "H22" as (a22) "(%Ha22 & H22)". subst a22.
  iDestruct "H23" as (a23) "(%Ha23 & H23)". subst a23.
  iDestruct "H24" as (a24) "(%Ha24 & H24)". subst a24.
  iDestruct "H25" as (a25) "(%Ha25 & H25)". subst a25.
  iDestruct "H26" as (a26) "(%Ha26 & H26)". subst a26.
  iDestruct "H27" as (a27) "(%Ha27 & H27)". subst a27.
  iSplitL "H8"; first (iExists v8; iFrame; iPureIntro; exact Hv8).
  iSplitL "H9"; first (iExists v9; iFrame; iPureIntro; exact Hv9).
  iSplitL "H18"; first (iExists v18; iFrame; iPureIntro; exact Hv18).
  iSplitL "H19"; first (iExists v19; iFrame; iPureIntro; exact Hv19).
  iSplitL "H20"; first (iExists v20; iFrame; iPureIntro; exact Hv20).
  iSplitL "H21"; first (iExists v21; iFrame; iPureIntro; exact Hv21).
  iSplitL "H22"; first (iExists v22; iFrame; iPureIntro; exact Hv22).
  iSplitL "H23"; first (iExists v23; iFrame; iPureIntro; exact Hv23).
  iSplitL "H24"; first (iExists v24; iFrame; iPureIntro; exact Hv24).
  iSplitL "H25"; first (iExists v25; iFrame; iPureIntro; exact Hv25).
  iSplitL "H26"; first (iExists v26; iFrame; iPureIntro; exact Hv26).
  iSplitL "H27"; first (iExists v27; iFrame; iPureIntro; exact Hv27).
  done.
Qed.
