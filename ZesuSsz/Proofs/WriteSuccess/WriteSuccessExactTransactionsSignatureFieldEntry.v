Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.RegPacking.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSignatureLoads WriteSuccessExactTransactionsFieldLoads
  WriteSuccessExactTransactionsGasLoads.

Definition transactionSignatureFieldCaller `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  (reg_col [(KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
     (KindReg "x26", BitsShape 64); (KindReg "x8", BitsShape 64)] ∗
   (bv_unsigned sp + 272) ↦ₘ? 8 ∗
   ⌜(index + 288 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureFieldCaller) := I.

Definition transactionSignatureFieldRetained `{!islaG Sigma} `{!threadG}
    (sp row : bv 64) (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 224) ↦ₘ (transactionRowWord bytes index 152) ∗
   (bv_unsigned sp + 232) ↦ₘ (transactionRowWord bytes index 144) ∗
   (bv_unsigned sp + 240) ↦ₘ (transactionRowWord bytes index 136) ∗
   ⌜bv_unsigned row `mod` 8 = 0⌝ ∗
   ⌜(index + 288 <= length bytes)%nat⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureFieldRetained) := I.

Lemma transactions_signature_field_entry `{!islaG Sigma} `{!threadG}
    sp row base bytes index (P : iProp Sigma) :
  transactionSignatureLoadPost sp row base bytes index
    (transactionSignatureFieldCaller sp bytes index P) -∗
  transactionFieldLoadEntry sp row base bytes index
    (transactionSignatureFieldRetained sp row bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionSignatureLoadPost) in "Hpost".
  iDestruct "Hpost" as "(Hsys & Hsp & Hrow & H11 & Hbytes & H152 & H144 & H136 &
    %Hcursor & %Hlength & %Hrowalign & %Hmin & %Hmax & %Hspalign &
    %Hspmin & %Hspmax & Hcaller & _)".
  iEval (rewrite /transactionSignatureFieldCaller) in "Hcaller".
  iDestruct "Hcaller" as "(Hothers & Hnonce & %HrowLength & %HstackHigh & HP & _)".
  iAssert (reg_col [(KindReg "x11", BitsShape 64); (KindReg "x12", BitsShape 64);
    (KindReg "x13", BitsShape 64); (KindReg "x26", BitsShape 64); (KindReg "x8", BitsShape 64)])%I
    with "[H11 Hothers]" as "Hregs".
  { iApply (reg_col_mixed_collect [("x11", transactionRowWord bytes index 152)] []
      [(KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
       (KindReg "x26", BitsShape 64); (KindReg "x8", BitsShape 64)]).
    - solve_Permutation.
    - iFrame. rewrite big_sepL_nil reg_col_nil. done. }
  rewrite /transactionFieldLoadEntry /transactionSignatureFieldRetained.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_signature_field_entry.
