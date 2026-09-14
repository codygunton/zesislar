Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactAuthorizationsInitialZero.

Lemma transactions_authorization_zero_complete_code `{!islaG Sigma} `{!threadG}
    sp pointer tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  instr_body 0x15584 (authorizationZeroEntry sp pointer tail P).
Proof.
  iStartProof. iIntros "#Hcode".
  iEval (unfold writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as
    "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iApply authorization_initial_zero.
  iApply instr_lookup_collect; last iExact "Hlookup".
  repeat constructor; reflexivity.
Qed.
Print Assumptions transactions_authorization_zero_complete_code.
