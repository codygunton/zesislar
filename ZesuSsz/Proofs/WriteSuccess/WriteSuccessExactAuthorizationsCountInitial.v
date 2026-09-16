Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.RegCollections.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsInitial WriteSuccessExactAuthorizationsLoopSpec
  WriteSuccessExactAuthorizationsCount WriteSuccessExactTransactionsMaxBlobFeeCount.

Definition authorizationFeeFrame `{!islaG Sigma} `{!threadG}
    (sp low high : bv 64) (rest : list (list (bv 8))) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 144) ↦ₘ high ∗ (bv_unsigned sp + 152) ↦ₘ low ∗
   (bv_unsigned sp + 160) ↦ₘ (Z_to_bv 64 (Z.of_nat (S (length rest)))) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationFeeFrame) := I.

Definition authorizationInitialCaller `{!islaG Sigma} `{!threadG}
    (sp low high : bv 64) base row rest source tail (P : iProp Sigma) : iProp Sigma :=
  (reg_col [(KindReg "x8", BitsShape 64); (KindReg "x9", BitsShape 64)] ∗
   reg_col [(KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
     (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
   base ↦ₘ∗ source ∗ (bv_unsigned sp + 1744) ↦ₘ? 144 ∗
   (bv_unsigned sp - 48) ↦ₘ? 16 ∗
   (bv_unsigned sp + 168) ↦ₘ (Z_to_bv 64 base) ∗
   ⌜authorizationLoopFacts sp (Z_to_bv 64 base) base (row :: rest) [] row rest source⌝ ∗
   P ∗ instr_pre 0x15620 (authorizationLoopExit sp base source tail
     (authorizationInitialFrame sp base (authorizationFeeFrame sp low high rest P))) ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationInitialCaller) := I.

Lemma authorization_count_to_initial `{!islaG Sigma} `{!threadG}
    (sp low high : bv 64) base row rest source tail (P : iProp Sigma) :
  authorizationCountPost sp (Z_to_bv 64 (Z.of_nat (S (length rest))))
    (WriteSuccessExactAuthorizationsModel.writeSuccessExactAuthorizationEvents sp (row :: rest) tail)
    (maxBlobFeeCountFrame sp low high (authorizationInitialCaller sp low high base row rest source tail P)) -∗
  (⌜authorizationLoopFacts sp (Z_to_bv 64 base) base (row :: rest) [] row rest source⌝ ∗
   authorizationInitialEntry sp (BV 64 0x15584) (BV 64 (mapIoContextAddress defaultMap)) base row rest source tail
     (authorizationFeeFrame sp low high rest P) ∗ True)%I.
Proof.
  iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hupper & Hmmio & Htrace & Hcountframe & _)".
  iDestruct "Hcountframe" as "(Hcountword & H18 & _ & _ & _ & Hfeeframe & _)".
  iDestruct "Hfeeframe" as "(Hmiddle & Hhighword & Hlowword & _ & _ & _ & Hcaller & _)".
  iDestruct "Hcaller" as "(H89 & Hothers & Hsource & Hcopy & Hlower & Hpointerword & %Hfacts & HP & Hexit & _)".
  iEval (replace (bv_unsigned sp - 32)%Z with (bv_unsigned sp - 48 + 16)%Z by lia) in "Hmiddle".
  iPoseProof (mem_mapsto_uninit_combine 16 (bv_unsigned sp - 48) (DfracOwn 1) 32
    with "Hlower Hmiddle") as "H32"; first lia.
  iEval (replace (bv_unsigned sp - 16)%Z with (bv_unsigned sp - 48 + 32)%Z by lia) in "Hupper".
  iPoseProof (mem_mapsto_uninit_combine 32 (bv_unsigned sp - 48) (DfracOwn 1) 48
    with "H32 Hupper") as "Hscratch"; first lia.
  iAssert (reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64)])
    with "[H10 H11]" as "Hpair".
  { rewrite !reg_col_cons reg_col_nil. iSplitL "H10".
    - iExists _. iFrame. done.
    - iSplitL "H11"; last done. iExists _. iFrame. done. }
  iPoseProof (zesu_reg_col_append with "[$Hpair $Hothers]") as "Hregs".
  iSplit; first (iPureIntro; exact Hfacts).
  unfold authorizationInitialEntry, authorizationInitialFrame, authorizationFeeFrame.
  iFrame.
Qed.
Print Assumptions authorization_count_to_initial.
