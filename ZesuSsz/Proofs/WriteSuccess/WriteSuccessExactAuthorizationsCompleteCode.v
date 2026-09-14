Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.BlockCodeLookup.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactAuthorizationsPublic.

Lemma authorization_complete_loop_code `{!islaG Sigma} `{!threadG} :
  writeSuccessCompleteNativeCode -∗ authorizationLoopCode.
Proof.
  iStartProof. iIntros "#Hcode".
  iEval (unfold writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as
    "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  unfold authorizationLoopCode.
  do 8 (iEval (rewrite big_sepL_cons); iSplit;
    [iApply instr_lookup_collect; last iExact "Hlookup"; repeat constructor; reflexivity |]).
  iEval (rewrite big_sepL_cons).
  iSplit; first iExact "Hmemcpy".
  iEval (rewrite big_sepL_cons).
  iSplit; first iExact "Hint".
  iEval (rewrite big_sepL_cons).
  iSplit; first iExact "Hu256".
  iEval (rewrite big_sepL_cons).
  iSplit; [iExact "Houtput" | done].
Qed.
Print Assumptions authorization_complete_loop_code.
